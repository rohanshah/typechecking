{-#LANGUAGE DeriveDataTypeable#-}

import Prelude hiding (error)
import Control.Exception
import Data.Typeable
import System.IO.Unsafe

---- Description --------------------------------------------------------------

-- The pure simply typed lambda calculus with recursive types

-- The type checking algorithm is implemented for equi-recursive types

---- Types and Terms -----------------------------------------------------------

data Ty = TyId String
        | TyVar Int Int
		| TyArr Ty Ty
        | TyRec String Ty
        deriving (Eq,Show)

data Term = TmVar Int Int
          | TmAbs Var Ty Term
          | TmApp Term Term
          deriving (Eq,Show)

tymap :: (Int -> Int -> Int -> Ty) -> Int -> Ty -> Ty
tymap onvar c tyT = case tyT of
                      TyArr tyT1 tyT2 -> TyArr (tymap' c tyT1) (tymap' c tyT2)
                      TyVar x n -> onvar c x n
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
            _ -> False

eval :: Term -> Term
eval t = case t of
               TmApp t1@(TmAbs x tyT1 t12) t2
                 | isval t2 -> termSubstTop t2 t12
                 | otherwise -> eval (TmApp t1 (eval t2))
               TmApp t1 t2 -> eval (TmApp (eval t1) t2)

---- Contexts ------------------------------------------------------------------

data Binding = NameBind
             | VarBind Ty
             | TyVarBind
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

computeType :: Ty -> Ty
computeType tyT = case tyT of
                    tyT1@(TyRec x tyT11) -> typeSubstTop tyT1 tyT11
                    _                    -> tyT

simplifyType :: Ty -> Ty
simplifyType tyT = let tyT' = computeType tyT in simplifyType tyT'

typeEquivalence :: [(Ty, Ty)] -> Context -> Ty -> Ty -> Bool
typeEquivalence seen ctx tyS tyT =
  (tyS, tyT) `elem` seen || case (tyS, tyT) of
    (TyRec x tyS1, _) -> typeEquivalence ((tyS, tyT):seen) ctx (typeSubstTop tyS tyS1) tyT
    (_, TyRec x tyT1) -> typeEquivalence ((tyS, tyT):seen) ctx tyS (typeSubstTop tyT tyT1)
    (TyId n1, TyId n2) -> n1 == n2
    (TyArr tyS1 tyS2, TyArr tyT1 tyT2) -> (typeEquivalence seen ctx tyS1 tyT1)
                                       && (typeEquivalence seen ctx tyS2 tyT2)
    _ -> False

---- Typechecking --------------------------------------------------------------

typeof :: Context -> Term -> Ty
typeof ctx t = case t of
                 TmVar i _ -> getTypeFromContext ctx i
                 TmAbs x tyT1 t2 -> let ctx' = addbinding ctx x (VarBind tyT1) in
                                    let tyT2 = typeof ctx' t2 in
                                    TyArr tyT1 (typeShift (-1) tyT2)
                 TmApp t1 t2 -> let tyT1 = typeof ctx t1 in
                                let tyT2 = typeof ctx t2 in
                                case simplifyType tyT1 of
                                  TyArr tyT11 tyT12 ->
                                    if typeEquivalence [] ctx tyT2 tyT11 then tyT12
                                    else error "parameter type mismatch"
                                  _ -> error "arrow type expected"

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
