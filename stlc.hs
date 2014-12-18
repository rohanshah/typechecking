{-#LANGUAGE DeriveDataTypeable#-}

import Prelude hiding (error)
import Control.Exception
import Data.Typeable
import System.IO.Unsafe

---- Description --------------------------------------------------------------

-- The simply typed lambda calculus with booleans, numbers, unit, ascription,
-- let-polymorphism, records, fixpoint, references, and errors

-- The type checking algorithm incorporates some basic Subtyping and
-- the type Top

---- Types and Terms -----------------------------------------------------------

data Ty = A
        | TyUnit
		| TyTop
        | TyBool
		| TyNum
		| TyArr Ty Ty
        | TyRcd [(Label, Ty)]
        | TyRef Ty
        | TyBot
        deriving (Eq,Show)

data Term = TmVar Int Int
          | TmAbs Var Ty Term
          | TmApp Term Term
          | TmTrue
          | TmFalse
          | TmIf Term Term Term
		  | TmZero
		  | TmSucc Term
          | TmPred Term
          | TmIsZero Term
          | TmUnit
          | TmAs Term Ty
          | TmLet Var Term Term
          | TmRcd [(Label, Term)]
          | TmProj Term Label
          | TmFix Term
          | TmLoc Int
          | TmRef Term
          | TmDeref Term
          | TmAssign Term Term
          | TmError
          | TmTry Term Term

---- Contexts ------------------------------------------------------------------

data Binding = NameBind
             | VarBind Ty

type Context = [(Var, Binding)]

addbinding :: Context -> Var -> Binding -> Context
addbinding ctx x bind = (x,bind):ctx

getbinding :: Context -> Int -> Binding
getbinding ctx i = case (ctx `atIndex` i)  of
                        Just (_, bind) -> bind
                        Nothing        -> error ("Variable lookup failure: offset: " ++ (show i) ++ ", ctx size " ++ (show (length ctx)))

getTypeFromContext :: Context -> Int -> Ty
getTypeFromContext ctx i = case getbinding ctx i of
                                VarBind ty -> ty
                                _          -> error "getTypeFromContext: Wrong kind of binding for variable"

---- Typechecking --------------------------------------------------------------

subtype :: Ty -> Ty -> Bool
subtype tyS tyT = tyS == tyT ||
                  case (tyS, tyT) of
                    (_, TyTop) -> True
                    (TyBot, _) -> True
                    (TyArr tyS1 tyS2, TyArr tyT1 tyT2) -> subtype tyT1 tyS1 && subtype tyS2 tyT2
                    (TyRcd s, TyRcd t) -> all (\(label, tyTi) ->
                      case lookup label s of
                        Just tySi -> subtype tySi tyTi
                        Nothing -> False) t
                    (TyRef tyT1, TyRef tyT2) -> subtype tyT1 tyT2 && subtype tyT2 tyT1
                    (_,_) -> False

typeof :: Context -> Term -> Ty
typeof ctx tm = case tm of
                  TmVar i _ -> getTypeFromContext ctx i
                  TmAbs x tyT1 t2 -> let ctx' = addbinding ctx x (VarBind tyT1) in
                                        let tyT2 = typeof ctx' t2 in
                                        TyArr tyT1 tyT2
                  TmApp t1 t2 -> let tyT1 = typeof ctx t1 in
                                    let tyT2 = typeof ctx t2 in
                                    case tyT1 of
                                      TyArr tyT11 tyT12 -> if subtype tyT2 tyT11
                                                           then tyT12
                                                           else error "parameter type mismatch"
                                      TyBot -> TyBot
                                      _ -> error "arrow type expected"
                  TmTrue -> TyBool
                  TmFalse -> TyBool
                  TmIf t1 t2 t3 -> if typeof ctx t1 == TyBool
                                      then let tyT2 = typeof ctx t2 in
                                        if tyT2 == typeof ctx t3 then tyT2
                                        else error "arms of conditional have different types"
                                      else error "guard of conditional not a boolean"
                  TmZero -> TyNum
                  TmSucc t1 -> if typeof ctx t1 == TyNum
                                  then TyNum
                                  else error "Succ should only be applied to a TyNum"
                  TmPred t1 -> if typeof ctx t1 == TyNum
                                  then TyNum
                                  else error "Pred should only be applied to a TyNum"
                  TmIsZero t1 -> if typeof ctx t1 == TyNum
                                  then TyBool
                                  else error "IsZero should only be applied to a TyNum"
                  TmUnit -> TyUnit
                  TmAs t1 tyT -> if typeof ctx t1 == tyT
                                    then tyT
                                    else error "Wrong type ascribed to term"
                  TmLet x t1 t2 -> let ctx' = addbinding ctx x
                                                   (VarBind (typeof ctx t1)) in
                                                 typeof ctx' t2
                  TmRcd fields -> let fieldtys =  map (\(label, ti) -> (label, typeof ctx ti)) fields in
                                     TyRcd fieldtys
                  TmProj t1 l -> let tyT1 = typeof ctx t1 in
                                    case tyT1 of
                                      TyRcd xs -> case lookup l xs of
                                                    Just ty -> ty
                                                    Nothing -> error "label not found in record"
                                      TyBot -> TyBot
                                      _ -> error "expected a record type for a projection"
                  TmFix t1 -> let tyT1 = typeof ctx t1 in
                                 case tyT1 of
                                   TyArr tyT11 tyT12 -> if tyT11 == tyT12
                                                        then tyT11
                                                        else error "fixpoint recursive functions need to be an arrow type of the form A -> A"
                                   _ -> error "arrow type expected for fixpoint recursion"
                  TmRef t1 -> TyRef (typeof ctx t1)
                  TmDeref t1 -> case typeof ctx t1 of
                                  TyRef tyT1 -> tyT1
                                  _ -> error "tried dereferencing a non-reference term"
                  TmAssign t1 t2 -> let tyT1 = typeof ctx t1 in
                                    let tyT2 = typeof ctx t2 in
                                      case tyT1 of
                                        TyRef tyT11 -> if tyT2 == tyT11
                                                       then tyT11
                                                       else error "type mismatch: a reference cell can only be assigned a term of its type"
                                        _ -> error "cannot assign a term to a non-reference cell"
                  TmError -> TyBot
                  TmTry t1 t2 -> let tyT1 = typeof ctx t1 in
                                 let tyT2 = typeof ctx t2 in
                                 if tyT1 == tyT2
                                 then tyT1
                                 else error "try catch blocks need to have the same type"

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
