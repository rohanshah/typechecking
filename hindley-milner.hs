{-#LANGUAGE DeriveDataTypeable#-}

import Prelude hiding (error)
import Control.Exception
import Data.Typeable
import System.IO.Unsafe

---- Description --------------------------------------------------------------

-- The simply typed lambda calculus with booleans and numbers

-- The type checking algorithm performs type reconstruction via the popular
-- Hindley-Milner unification algorithm 

---- Types and Terms -----------------------------------------------------------

data Ty = TyBool
		| TyNat
		| TyArr Ty Ty
        | TyId String
        deriving (Eq,Show)

data Term = TmVar Int Int
          | TmLet Var Term Term
          | TmTrue
          | TmFalse
          | TmIf Term Term Term
		  | TmZero
		  | TmSucc Term
          | TmPred Term
          | TmIsZero Term
          | TmAbs Var (Maybe Ty) Term
          | TmApp Term Term
          deriving (Eq,Show)

occursIn :: Var -> Ty -> Bool
occursIn x ty = case ty of
                  TyId y -> x == y
                  TyArr tyT1 tyT2 -> x `occursIn` tyT1 || x `occursIn` tyT2
                  _ -> False

substTy :: Var -> Ty -> Ty -> Ty
substTy x tyS tyT = case tyT of
                      TyNat -> TyNat
                      TyBool -> TyBool
                      TyArr tyT1 tyT2 ->
                        TyArr (substTy x tyS tyT1) (substTy x tyS tyT2)
                      TyId y -> if x == y then tyS else TyId y

---- Contexts ------------------------------------------------------------------

data Binding = NameBind
             | VarBind Ty
             deriving (Eq,Show)

type Context = [(Var, Binding)]

index2name :: Context -> Int -> Var
index2name ctx i = case (ctx `atIndex` i)  of
                        Just (var, _) -> var
                        Nothing        -> error ("Variable lookup failure: offset: " ++ (show i) ++ ", ctx size " ++ (show (length ctx)))

addbinding :: Context -> Var -> Binding -> Context
addbinding ctx x bind = (x,bind):ctx

getbinding :: Context -> Int -> Binding
getbinding ctx i = case (ctx `atIndex` i)  of
                        Just (_, bind) -> bind
                        Nothing        -> error ("Variable lookup failure: offset: " ++ (show i) ++ ", ctx size " ++ (show (length ctx)))

getTypeFromContext :: Context -> Int -> Ty
getTypeFromContext ctx i = case getbinding ctx i of
                                VarBind ty -> ty
                                _          -> error ("getTypeFromContext: Wrong kind of binding for variable " ++ (index2name ctx i))

---- Constraints ---------------------------------------------------------------

type Constraint = [(Ty, Ty)]

data NextUVar = NextUVar String UVarGenerator
type UVarGenerator = () -> NextUVar

uvargen :: () -> NextUVar
uvargen = let uvargen' n () = NextUVar ("?X_"++(show n)) (uvargen' (n+1))
          in uvargen' 0

substConst :: Constraint -> Var -> Ty -> Constraint
substConst cst x tyT = map (\(tyS1, tyS2) ->
                             (substTy x tyT tyS1, substTy x tyT tyS2))
                           cst

applySubst :: Ty -> Constraint -> Ty
applySubst tyT cst = foldl (\tyT' (TyId x, tyS) -> substTy x tyS tyT')
                          tyT (reverse cst)

unify :: Constraint -> Constraint
unify cst = case cst of
              [] -> []
              (TyNat, TyNat):cst' -> unify cst'
              (TyBool, TyBool):cst' -> unify cst'
              (TyArr tyS1 tyS2, TyArr tyT1 tyT2):cst' ->
                unify [(tyS1,tyT1), (tyS2, tyT2)]++cst'
              (TyId x, tyT):cst' ->
                if tyT == (TyId x)
                then unify cst'
                else if x `occursIn` tyT
                     then error "Circular constraints"
                     else (unify $ substConst cst' x tyT)++[(TyId x, tyT)]
              (tyS, TyId x):cst' ->
                if tyS == (TyId x)
                then unify cst'
                else if x `occursIn` tyS
                     then error "Circular constraints"
                     else (unify $ substConst cst' x tyS)++[(TyId x, tyS)]
              _ -> error "Unsolvable constraints"

---- Typechecking --------------------------------------------------------------

typeof :: Term -> Ty
typeof tm = case reconstruct [] tm uvargen of
              (tyT, _, cst) -> let cst' = unify cst in applySubst tyT cst'

reconstruct :: Context
            -> Term
            -> (() -> NextUVar)
            -> (Ty, (() -> NextUVar), Constraint)
reconstruct ctx tm nuv =
  case tm of
    TmVar i _ ->
      let ty = getTypeFromContext ctx i
      in (ty, nuv, [])
    TmAbs x (Just tyT1) t2 ->
      let ctx' = addbinding ctx x (VarBind tyT1) in
      let (tyT2, nuv', cst') = reconstruct ctx' t2 nuv in
      (TyArr tyT1 tyT2, nuv', cst')
    TmAbs x Nothing t2 ->
      let (NextUVar var nuv') = nuv () in
      let tyT1 = TyId var in
      let ctx' = addbinding ctx x (VarBind tyT1) in
      let (tyT2, nuv'', cst') = reconstruct ctx' t2 nuv' in
      (TyArr tyT1 tyT2, nuv', cst')
    TmApp t1 t2 ->
      let (tyT1, nuv', cst) = reconstruct ctx t1 nuv in
      let (tyT2, nuv'', cst') = reconstruct ctx t2 nuv' in
      let (NextUVar var nuv''') = nuv'' () in
      let tyX = TyId var in
      let constr = (tyT1, TyArr tyT2 tyX) in
      let cst'' = constr:(cst++cst') in
      (tyX, nuv''', cst'')
    TmZero -> (TyNat, nuv, [])
    TmSucc t1 ->
      let (tyT1, nuv', cst) = reconstruct ctx t1 nuv in
      let cst' = (tyT1, TyNat):cst in
      (TyNat, nuv', cst')
    TmPred t1 ->
      let (tyT1, nuv', cst) = reconstruct ctx t1 nuv in
      let cst' = (tyT1, TyNat):cst in
      (TyNat, nuv', cst')
    TmIsZero t1 ->
      let (tyT1, nuv', cst) = reconstruct ctx t1 nuv in
      let cst' = (tyT1, TyNat):cst in
      (TyBool, nuv', cst')
    TmTrue -> (TyBool, nuv, [])
    TmFalse -> (TyBool, nuv, [])
    TmIf t1 t2 t3 ->
      let (tyT1, nuv', cst) = reconstruct ctx t1 nuv in
      let (tyT2, nuv'', cst') = reconstruct ctx t2 nuv' in
      let (tyT3, nuv''', cst'') = reconstruct ctx t3 nuv'' in
      let cst''' = [(tyT1, TyBool), (tyT2, tyT3)] in
      let cst'''' = cst++cst'++cst''++cst''' in
      (tyT2, nuv''', cst'''')
    TmLet x t1 t2 ->
      let (tyT1, nuv', cst) = reconstruct ctx t1 nuv in
      let ctx' = addbinding ctx x (VarBind tyT1) in
      let (tyT2, nuv'', cst') = reconstruct ctx' t2 nuv' in
      let cst'' = cst++cst'' in
      (tyT2, nuv'', cst'')

---- Auxiliary -----------------------------------------------------------------

type Label = String
type Var = String

data Exit = Exit Int
            deriving (Show, Typeable)

instance Exception Exit

error :: String -> a
error s = unsafePerformIO $ do putStr $ s ++ "\n"
                               return $ throw (Exit 1)

atIndex :: [a] -> Int -> Maybe a
atIndex l i = if i >= length l || i < 0
              then Nothing
              else Just (l !! i)
