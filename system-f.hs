{-#LANGUAGE DeriveDataTypeable#-}

import Prelude hiding (error)
import Control.Exception
import Data.Typeable
import System.IO.Unsafe

---- Description --------------------------------------------------------------

-- System F (Kernel): The pure simply typed lambda calculus with universal and
-- existential types as well as bounded quantification and subtyping

---- Types and Terms -----------------------------------------------------------

data Ty = TyVar Int Int
		| TyArr Ty Ty
        | TyAll TVar Ty Ty
		| TySome TVar Ty Ty
		| TyTop
        deriving (Eq,Show)

data Term = TmVar Int Int
          | TmAbs Var Ty Term
          | TmApp Term Term
          | TmTAbs TVar Ty Term
          | TmTApp Term Ty
          | TmPack Ty Term Ty
          | TmUnpack TVar Var Term Term
          deriving (Eq,Show)

tymap :: (Int -> Int -> Int -> Ty) -> Int -> Ty -> Ty
tymap onvar c tyT = case tyT of
                      TyArr tyT1 tyT2 -> TyArr (tymap' c tyT1) (tymap' c tyT2)
                      TyVar x n -> onvar c x n
                      TyAll tyX tyT1 tyT2 -> TyAll tyX (tymap' c tyT1) (tymap' (c+1) tyT2)
                      TySome tyX tyT1 tyT2 -> TySome tyX (tymap' c tyT1) (tymap' (c+1) tyT2)
                    where tymap' = tymap onvar

typeShiftAbove :: Int -> Int -> Ty -> Ty
typeShiftAbove d c tyT = tymap (\c x n -> if x >= c
                                          then if x+d < 0
                                               then error "Scoping error!"
                                               else TyVar (x+d) (n+d)
                                          else TyVar x (n+d)
                               ) c tyT

typeShift :: Int -> Ty -> Ty
typeShift c tyT = typeShiftAbove 0 c tyT

typeSubst :: Ty -> Int -> Ty -> Ty
typeSubst tyS j tyT = tymap (\j x n -> if x == j
                                       then typeShift j tyS
                                       else TyVar x n
                            ) j tyT

typeSubstTop :: Ty -> Ty -> Ty
typeSubstTop tyS tyT = typeShift (-1) (typeSubst (typeShift 1 tyS) 0 tyT)

tmmap :: (Int -> Int -> Int -> Term) -> (Int -> Ty -> Ty) -> Int -> Term -> Term
tmmap onvar ontype c t = case t of
                           TmVar x n -> onvar c x n
                           TmAbs x tyT1 t2 -> TmAbs x (ontype c tyT1) (tmmap' (c+1) t2)
                           TmApp t1 t2 -> TmApp (tmmap' c t1) (tmmap' c t2)
                           TmTAbs tyX tyT1 t2 -> TmTAbs tyX (ontype c tyT1) (tmmap' (c+1) t2)
                           TmTApp t1 tyT2 -> TmTApp (tmmap' c t1) (ontype c tyT2)
                           TmPack tyT1 t2 tyT3 -> TmPack (ontype c tyT1) (tmmap' c t2) (ontype c tyT3)
                           TmUnpack tyX x t1 t2 -> TmUnpack tyX x (tmmap' c t1) (tmmap' (c+2) t2)
                         where tmmap' = tmmap onvar ontype

termShiftAbove :: Int -> Int -> Term -> Term
termShiftAbove d c t = tmmap (\c x n -> if x >= c
                                        then TmVar (x+d) (n+d)
                                        else TmVar x (n+d)
                             ) (typeShiftAbove d) c t

termShift :: Int -> Term -> Term
termShift d t = termShiftAbove d 0 t

termSubst :: Int -> Term -> Term -> Term
termSubst j s t = tmmap (\j x n -> if x == j
                                   then termShift j s
                                   else TmVar x n
                        ) (\j tyT -> tyT) j t

tytermSubst :: Ty -> Int -> Term -> Term
tytermSubst tyS j t = tmmap (\c x n -> TmVar x n) (\j tyT -> typeSubst tyS j tyT) j t

termSubstTop :: Term -> Term -> Term
termSubstTop s t = termShift (-1) (termSubst 0 (termShift 1 s) t)

tytermSubstTop :: Ty -> Term -> Term
tytermSubstTop tyS t = termShift (-1) (tytermSubst (typeShift 1 tyS) 0 t)

isval :: Term -> Bool
isval t = case t of
            TmAbs _ _ _ -> True
            TmTAbs _ _ _ -> True
            TmPack _ t _ -> isval t
            _ -> False

eval :: Term -> Term
eval t = case t of
               TmApp t1@(TmAbs x tyT1 t12) t2
                 | isval t2 -> termSubstTop t2 t12
                 | otherwise -> eval (TmApp t1 (eval t2))
               TmApp t1 t2 -> eval (TmApp (eval t1) t2)
               TmTApp (TmTAbs _ _ t11) tyT2 -> tytermSubstTop tyT2 t11
               TmTApp t1 tyT2 -> eval (TmTApp (eval t1) tyT2)
               TmUnpack _ _ (TmPack tyT11 t12 _) t2
                 | isval t12 -> tytermSubstTop  tyT11 (termSubstTop (termShift 1 t12) t2)
               TmUnpack tyX x t1 t2 -> eval (TmUnpack tyX x (eval t1) t2)
               TmPack tyT1 t2 tyT3 -> eval (TmPack tyT1 (eval t2) tyT3)
               _ -> t

---- Contexts ------------------------------------------------------------------

data Binding = NameBind
             | VarBind Ty
             | TyVarBind Ty
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

bindingshift n bind = case bind of
                        NameBind -> NameBind
                        VarBind tyT -> VarBind (typeShift n tyT)
                        TyVarBind tyT-> TyVarBind (typeShift n tyT)

getTypeFromContext :: Context -> Int -> Ty
getTypeFromContext ctx i = case getbinding ctx i of
                                VarBind ty -> ty
                                _          -> error ("getTypeFromContext: Wrong kind of binding for variable " ++ (index2name ctx i))

promote :: Context -> Ty -> Ty
promote ctx tyS = case tyS of
                    TyVar n _ -> case getbinding ctx n of
                                   TyVarBind tyT -> tyT
                                   _ -> tyS
                    _ -> tyS

promoteRepeat :: Context -> Ty -> Ty
promoteRepeat ctx tyS = let tyT = promote ctx tyS in
                        if tyS == tyT
                        then tyT
                        else promoteRepeat ctx tyT

---- Typechecking --------------------------------------------------------------

subtype :: Context -> Ty -> Ty -> Bool
subtype ctx tyS tyT = tyS == tyT ||
  case (tyS, tyT) of
    (TyVar _ _, _) -> subtype ctx (promote ctx tyS) tyT
    (TyArr tyS1 tyS2, TyArr tyT1 tyT2) ->
      subtype ctx tyT1 tyS1 && subtype ctx tyS2 tyT2
    (TyAll tyX1 tyS1 tyS2, TyAll _ tyT1 tyT2) ->
      subtype ctx tyT1 tyS1 && subtype ctx tyS1 tyT1 &&
      subtype (addbinding ctx tyX1 (TyVarBind tyT1)) tyS2 tyT2
    (TySome tyX1 tyS1 tyS2, TySome _ tyT1 tyT2) ->
      subtype ctx tyT1 tyS1 && subtype ctx tyS1 tyT1 &&
      subtype (addbinding ctx tyX1 (TyVarBind tyT1)) tyS2 tyT2
    (_, TyTop) -> True
    (_,_) -> False

typeof :: Context -> Term -> Ty
typeof ctx t = case t of
                 TmVar i _ -> getTypeFromContext ctx i
                 TmAbs x tyT1 t2 -> let ctx' = addbinding ctx x (VarBind tyT1) in
                                    let tyT2 = typeof ctx' t2 in
                                    TyArr tyT1 (typeShift (-1) tyT2)
                 TmApp t1 t2 -> let tyT1 = typeof ctx t1 in
                                let tyT2 = typeof ctx t2 in
                                case promoteRepeat ctx tyT1 of
                                  TyArr tyT11 tyT12 -> if subtype ctx tyT2 tyT11
                                                          then tyT12
                                                          else error "parameter type mismatch"
                                  _ -> error "arrow type expected"
                 TmTAbs tyX tyT1 t2 -> let ctx' = addbinding ctx tyX (TyVarBind tyT1) in
                                  let tyT2 = typeof ctx' t2 in
                                  TyAll tyX tyT1 tyT2
                 TmTApp t1 tyT2 -> let tyT1 = typeof ctx t1 in
                                   case promoteRepeat ctx tyT1 of
                                     TyAll _ tyT11 tyT12 ->
                                       if not (subtype ctx tyT2 tyT11)
                                       then error "parameter type mismatch"
                                       else typeSubstTop tyT2 tyT12
                                     _ -> error "universal type expected"
                 TmPack tyT1 t2 tyT -> case tyT of
                                         TySome tyY tyTY tyT2 ->
                                           if not (subtype ctx tyT1 tyTY)
                                           then error "hidden type is not a subtype of the bound"
                                           else let tyU = typeof ctx t2 in
                                           let tyU' = typeSubstTop tyT1 tyT2 in
                                           if tyU == tyU'
                                           then tyT
                                           else error "doesn't match declared type"
                                         _ -> error "existential type expected"
                 TmUnpack tyX x t1 t2 -> let tyT1 = typeof ctx t1 in
                                         case tyT1 of
                                           TySome tyY tyTY tyT11 ->
                                             let ctx' = addbinding ctx tyX (TyVarBind tyTY) in
                                             let ctx'' = addbinding ctx' x (VarBind tyT11) in
                                             let tyT2 = typeof ctx'' t2 in
                                             typeShift (-2) tyT2
                                           _ -> error "existential type expected"

---- Auxiliary -----------------------------------------------------------------

type Label = String
type Var = String
type TVar = String

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
