{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# OPTIONS_GHC -Wno-deprecations #-}
module Horn.Nano.Nano where

import qualified Horn.Logic.Clauses as L
import           Language.ECMAScript3.Syntax 
import           Language.ECMAScript3.PrettyPrint
import           Text.PrettyPrint.ANSI.Leijen       (text,(<+>))
import           Language.ECMAScript3.Parser        (parseJavaScriptFromFile)
import           Data.Maybe                         
import           Text.Parsec                    
import qualified Data.Set    as Set
import           Data.Set    (Set)
import           Data.Generics                      (Data)
import           Data.Typeable                      (Typeable)

data Exp = Var String
              | Num Integer
              | Plus Exp Exp
              | Minus Exp Exp 
              | Times Exp Exp deriving (Show,Eq,Ord)

data BExp = Bool Bool
              | And BExp BExp
              | Or BExp BExp
              | Lte Exp Exp                 -- less than or equal
              | Gte Exp Exp                 -- greater than or equal
              | Eq Exp Exp                  -- equal
              | Neq Exp Exp deriving (Show) -- not equal

data Stmt = Skip
              | Assign String Exp         -- x := e
              | Seq Stmt Stmt             -- s1;s2
              | SeqList [Stmt]            -- [s1,s2,...]
              | If BExp Stmt Stmt         -- if b s1 s2
              | While L.Base BExp Stmt    -- while [inv] b s
              | Assume L.Base             
              | Assert L.Base deriving (Show)



-------------------------------------
getVarsExp :: Exp -> Set L.Var
-------------------------------------
getVarsExp (Var s) = Set.singleton $ L.Var s

getVarsExp (Num _) = Set.empty

getVarsExp (Plus e1 e2) = Set.union vs1 vs2
  where
    vs1 = getVarsExp e1
    vs2 = getVarsExp e2

getVarsExp (Minus e1 e2) = Set.union vs1 vs2
  where
    vs1 = getVarsExp e1
    vs2 = getVarsExp e2

getVarsExp (Times e1 e2) = Set.union vs1 vs2
  where
    vs1 = getVarsExp e1
    vs2 = getVarsExp e2

-------------------------------------
getVarsBExp :: BExp -> Set L.Var
-------------------------------------

getVarsBExp (Bool _) = Set.empty

getVarsBExp (And e1 e2) = Set.union vs1 vs2
  where
    vs1 = getVarsBExp e1
    vs2 = getVarsBExp e2

getVarsBExp (Or e1 e2) = Set.union vs1 vs2
  where
    vs1 = getVarsBExp e1
    vs2 = getVarsBExp e2    

getVarsBExp (Lte e1 e2) = Set.union vs1 vs2
  where
    vs1 = getVarsExp e1
    vs2 = getVarsExp e2   

getVarsBExp (Gte e1 e2) = Set.union vs1 vs2
  where
    vs1 = getVarsExp e1
    vs2 = getVarsExp e2   

getVarsBExp (Eq e1 e2) = Set.union vs1 vs2
  where
    vs1 = getVarsExp e1
    vs2 = getVarsExp e2   

getVarsBExp (Neq e1 e2) = Set.union vs1 vs2
  where
    vs1 = getVarsExp e1
    vs2 = getVarsExp e2   

-------------------------------------
getVars :: Stmt -> Set L.Var
-------------------------------------

getVars Skip = Set.empty

getVars (Assign x e) = Set.union vs1 vs2
    where
      vs1 = Set.singleton $ L.Var x
      vs2 = getVarsExp e

getVars (Seq s1 s2) = Set.union vs1 vs2
    where
      vs1 = getVars s1
      vs2 = getVars s2

getVars (SeqList ss) = Set.unions $ map getVars ss

getVars (If e s1 s2) = Set.unions [vse, vs1,vs2]
    where
      vse = getVarsBExp e
      vs1 = getVars s1
      vs2 = getVars s2

getVars (While b e s) = Set.unions [vsb, vse, vss]
    where
      vsb = L.get_vars b
      vse = getVarsBExp e
      vss = getVars s

getVars (Assume b) = L.get_vars b

getVars (Assert b) = L.get_vars b
-------------------------------------
expToBase :: Exp -> L.Exp
-------------------------------------              
-- expToBase _ = error "TODO: FILL THIS IN"
expToBase (Var a) = L.Var a

expToBase (Num a) = L.Num a

expToBase (Plus e1 e2) = L.Plus [e1', e2']
  where e1' = expToBase e1
        e2' = expToBase e2

expToBase (Minus e1 e2) = L.Minus [e1', e2']
  where e1' = expToBase e1
        e2' = expToBase e2

expToBase (Times e1 e2) = L.Times [e1', e2']
  where e1' = expToBase e1
        e2' = expToBase e2

-------------------------------------
bexpToBase :: BExp -> L.Base
-------------------------------------
-- bexpToBase (Bool b) 
--         | b==True   = L.Or  []
--         | b==False  = L.And []
bexpToBase (Bool True) = L.Tr
bexpToBase (Bool False) = L.Fl

-- bexpToBase _ = error "TODO: FILL THIS IN"
bexpToBase (And b1 b2) = L.And $ map bexpToBase [b1, b2]

bexpToBase (Or  b1 b2) = L.Or $ map bexpToBase [b1, b2]

bexpToBase (Lte b1 b2) = L.Leq (expToBase b1) (expToBase b2)

bexpToBase (Gte b1 b2) = L.Geq (expToBase b1) (expToBase b2)

bexpToBase (Eq  b1 b2) = L.Eq (expToBase b1) (expToBase b2)

bexpToBase (Neq b1 b2) = L.Neg (L.Eq (expToBase b1) (expToBase b2))
---------------------------------------------------------------------
-- | Parsing ESC/JAVA
---------------------------------------------------------------------

-- | `isNano` is a predicate that describes the **syntactic subset** 
--   of ECMAScript3 that comprises `Nano`.

class IsNano a where 
  isNano :: a -> Bool

instance IsNano InfixOp where
  isNano OpLAnd = True -- @&&@
  isNano OpLOr  = True -- @||@
  isNano OpLEq   = True -- @<@
  isNano OpGEq   = True -- @>@
  isNano OpSub  = True -- @-@
  isNano OpAdd  = True -- @+@
  isNano OpMul  = True -- @*@
  isNano OpEq   = True -- @==@
  isNano OpNEq  = True -- @!=@
  isNano _      = False

instance IsNano (LValue a) where 
  isNano (LVar _ _) = True
  isNano _          = False

instance IsNano AssignOp where
  isNano OpAssign = True
  isNano x        = error $ show $ text  "Not a Nano AssignOp!" <+> prettyPrint x

instance IsNano (Expression a) where 
  isNano (BoolLit _ _)         = True
  isNano (IntLit _ _)          = True
  isNano (VarRef _ _)          = True
  isNano (InfixExpr _ o e1 e2) = isNano o && isNano e1 && isNano e2
  isNano e                     = error $ show $ text "Not Nano Expression!" <+> prettyPrint e 

instance IsNano (Statement a) where
  isNano (EmptyStmt _)         = True                   -- skip
  isNano s
    | isSpecification s        = True
  isNano (ExprStmt _ e)        = isNanoExprStatement e  -- x = e
  isNano (BlockStmt _ ss)      = isNano ss              -- sequence
  isNano (IfSingleStmt _ b s)  = isNano b && isNano s   
  isNano (IfStmt _ b s1 s2)    = isNano b && isNano s1 && isNano s2
  isNano (WhileStmt _ b s)     = isNano b && isNano s
  isNano (VarDeclStmt _ ds)    = all isNano ds 
  isNano e                     = error $ show $ text "Not a Nano Statement!" <+> prettyPrint e

instance IsNano a => IsNano (Maybe a) where 
  isNano (Just x) = isNano x
  isNano Nothing  = True

instance IsNano [Statement a] where 
  isNano = all isNano

isNanoExprStatement :: Expression a -> Bool
isNanoExprStatement (AssignExpr _ o lv e) = isNano o && isNano lv && isNano e 
isNanoExprStatement e                     = error $ show $ text "Not Nano ExprStmt!" <+> prettyPrint e

instance IsNano (VarDecl a) where
  isNano (VarDecl _ _ (Just e)) = isNano e
  isNano (VarDecl _ _ Nothing)  = True

------------------------------------------
toNanoBexp :: Expression a -> BExp
------------------------------------------
-- toNanoBexp _ = error "TODO: FILL THIS IN"

toNanoBexp (BoolLit _ a) = Bool a

toNanoBexp (InfixExpr _ o e1 e2)
  | o==OpLAnd = And (toNanoBexp  e1) (toNanoBexp  e2) 
  | o==OpLOr  = Or  (toNanoBexp  e1) (toNanoBexp  e2) 
  | o==OpLEq  = Lte (toNanoExp  e1) (toNanoExp  e2) 
  | o==OpGEq  = Gte (toNanoExp  e1) (toNanoExp  e2)  
  | o==OpEq   = Eq  (toNanoExp  e1) (toNanoExp  e2)  
  | o==OpNEq  = Neq (toNanoExp  e1) (toNanoExp  e2)

------------------------------------------
toNanoExp :: Expression a -> Exp
------------------------------------------
-- toNanoExp _  = error "TODO: FILL THIS IN"

toNanoExp (VarRef _ (Id _ f)) = Var f

toNanoExp (IntLit _ a) = Num (toInteger a)

toNanoExp (InfixExpr _ o e1 e2)
  | o==OpSub  = Minus (toNanoExp  e1) (toNanoExp  e2)  
  | o==OpAdd  = Plus  (toNanoExp  e1) (toNanoExp  e2)  
  | o==OpMul  = Times (toNanoExp  e1) (toNanoExp  e2)

------------------------------------------
toNanoStmt :: Statement a -> Stmt
------------------------------------------
toNanoStmt (EmptyStmt _) = Skip

toNanoStmt s 
  | isAssume s = Assume $ fromJust $ getAssume s
  | isAssert s = Assert $ fromJust $ getAssert s
  | isInv s    = Skip

toNanoStmt (ExprStmt _ e) = f e
  where
    f (AssignExpr _ o lv e1) = Assign (f1 lv) (toNanoExp e1)
      where
        f1 (LVar _ s) = s

toNanoStmt (BlockStmt _ ss) = SeqList ss'
  where
    ss' = map toNanoStmt ss

toNanoStmt (IfSingleStmt e s1 s2) = Skip

toNanoStmt (IfStmt _ e s1 s2) = If e' s1' s2'
  where
    e'  = toNanoBexp e
    s1' = toNanoStmt s1
    s2' = toNanoStmt s2

toNanoStmt (WhileStmt _ b s) = While inv' b' s'
  where
    b'   = toNanoBexp b
    s'   = toNanoStmt s
    inv' = getInvariant s

toNanoStmt (VarDeclStmt _ ds) = SeqList $ map f ds
  where
    f (VarDecl _ (Id _ x) (Just e)) = Assign x (toNanoExp e)

---------------------------------------------------------------------
mkNano :: [Statement SourcePos] -> Maybe [Stmt]
---------------------------------------------------------------------
mkNano smts =  fmap concat $ sequence $ map mkNanoFun smts 

---------------------------------------------------------------------
mkNanoFun :: Statement a -> Maybe [Stmt]
---------------------------------------------------------------------
mkNanoFun (FunctionStmt l f xs body) 
  | all isNano body = Just $ nano
  | otherwise       = Nothing
  where 
    nano = map toNanoStmt body

mkNanoFun s = error $ show $ text "Conversion error" <+> prettyPrint s

-----------------------------------------------------------------------------------
-- | Helpers for extracting specifications from @ECMAScript3@ @Statement@ 
-----------------------------------------------------------------------------------

-- Ideally, a la JML, we'd modify the parser to take in annotations for 
-- 
--   * assert(p)
--   * assume(p)
--   * invariant(p) 
--
-- For now, we hack them with function calls.

isSpecification :: Statement a -> Bool
isSpecification s  = not $ null $ catMaybes $ ($ s) <$> specs 
  where 
    specs          = [getAssert, getAssume, getInv]

getInvariant :: Statement a -> L.Base
getInvariant = getSpec getInv . flattenStmt

flattenStmt (BlockStmt _ ss) = concatMap flattenStmt ss
flattenStmt s                = [s]

getAssume    :: Statement a -> Maybe L.Base
getAssume    = getStatementPred "assume"

isAssume     :: Statement a -> Bool 
isAssume     =  isJust . getAssume

getAssert    :: Statement a -> Maybe L.Base 
getAssert    = getStatementPred "assert"

isAssert     :: Statement a -> Bool 
isAssert     =  isJust . getAssert

getInv       = getStatementPred "invariant"

isInv     :: Statement a -> Bool 
isInv     =  isJust . getInv

-- extract assert, which is Q for validation
getStatementPred :: String -> Statement a -> Maybe L.Base
getStatementPred name (ExprStmt _ (CallExpr _ (VarRef _ (Id _ f)) [p]))
  | name == f = Just $ bexpToBase $ toNanoBexp p -- name == 'assert, assume, invariant'
getStatementPred _ _ = Nothing 

getSpec   :: (Statement a -> Maybe L.Base) -> [Statement a] -> L.Base
getSpec g stmts =  L.And $ catMaybes $ map g stmts


---------------------------------------------------------------------
-- | Command Line Configuration Options
---------------------------------------------------------------------

data Config = Config { 
    files   :: [FilePath]     -- ^ source files to check
  } deriving (Data, Typeable, Show, Eq)

-- ---------------------------------------------------------------------
-- -- | Top-level Parser 
-- ---------------------------------------------------------------------
parseNanoFromFile f = 
  do  s <- parseJavaScriptFromFile f
      return $ fromMaybe err (mkNano s)
  where
      err  = error $ show $ text "Invalid Input File"

-------------------------------------------
test :: IO ()
-------------------------------------------
test = do
    stmt <- parseNanoFromFile "tests/pos/while5.js"
    putStr $ "Parsed the file :  " ++ (show stmt)
    
    
