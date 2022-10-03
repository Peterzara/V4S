{-# LANGUAGE UnicodeSyntax #-}
module Horn.Logic.Clauses where
import           Data.List   (intercalate)
import           Data.Map    (Map)
import qualified Data.Map    as Map
import           Data.Maybe
import           Data.Set    (Set)
import qualified Data.Set    as Set
import           Control.Monad.State.Strict
import           Debug.Trace

data Exp =   Var String
            | Num Integer
            | Plus [Exp]
            | Minus [Exp]
            | Times [Exp]
            deriving (Eq,Ord)

data Base =   Tr                -- true
            | Fl                -- false
            | Eq Exp Exp        -- e1 = e2
            | Geq Exp Exp       -- e1 >= e2
            | Leq Exp Exp       -- e1 =< e2
            | Neg Base          -- not e
            | And [Base]        -- /\ [e1, e2, ...]
            | Or  [Base]        -- \/ [e1, e2, ...]
            | Implies Base Base -- F1 => F2
            deriving (Eq,Ord)

type Var = Exp

------------------
-- pretty printing
------------------
instance Show Base where
  show (Eq e1 e2)      = (show e1) ++ "=" ++ (show e2)
  show (Geq e1 e2)     = (show e1) ++ "≥" ++ (show e2)
  show (Leq e1 e2)     = (show e1) ++ "≤" ++ (show e2)
  show (Neg e)         = "¬" ++ (show e)
  show (And es)        = "(" ++ intercalate "∧" (map show es) ++ ")"
  show (Or es)         = intercalate "∨" (map show es)
  show (Implies e1 e2) = "(" ++ (show e1) ++ "⇒" ++ (show e2) ++ ")"
  show (Tr)          = "True"
  show (Fl)         = "False"

instance Show Exp where
  show (Var s)    = s
  show (Num n)    = (show n)
  show (Plus es)  = intercalate "+" (map show es)
  show (Minus es) = intercalate "-" (map show es)
  show (Times es) = intercalate "*" (map show es)


-- Helper functions

---------------------------
get_vars :: Base -> Set Exp
---------------------------
get_vars (Eq e1 e2)      = Set.union  (get_vars_exp e1) (get_vars_exp e2)
get_vars (Geq e1 e2)     = Set.union (get_vars_exp e1) (get_vars_exp e2)
get_vars (Leq e1 e2)     = Set.union (get_vars_exp e1) (get_vars_exp e2)
get_vars (Neg e)         = get_vars e
get_vars (And es)        = Set.unions $ map get_vars es
get_vars (Or es)         = Set.unions $ map get_vars es
get_vars (Implies e1 e2) = Set.union (get_vars e1) (get_vars e2)
get_vars (Tr)            = Set.empty
get_vars (Fl)            = Set.empty

------------------------------
get_vars_exp :: Exp -> Set Exp
------------------------------
get_vars_exp (Var s)    = Set.singleton (Var s)
get_vars_exp (Num n)    = Set.empty
get_vars_exp (Plus es)  = Set.unions $ map get_vars_exp es
get_vars_exp (Minus es) = Set.unions $ map get_vars_exp es
get_vars_exp (Times es) = Set.unions $ map get_vars_exp es

-------------------------------------
subst :: Exp -> Var -> Base ->  Base
-------------------------------------
-- subst  y x f = error "TODO: FILL THIS IN"
subst y x f = case f of (Tr)  -> f
                        (Fl)  -> f
                        (Eq e1 e2)  -> Eq (subst_exp y x e1) (subst_exp y x e2)
                        (Geq e1 e2) -> Eq (subst_exp y x e1) (subst_exp y x e2)
                        (Leq e1 e2) -> Eq (subst_exp y x e1) (subst_exp y x e2)
                        (Neg b) -> Neg (subst y x b)
                        (And bs) -> And $ map (subst y x) bs
                        (Or bs)  -> Or  $ map (subst y x) bs
                        (Implies b1 b2) -> Implies (subst y x b1) (subst y x b2)

---------------------------------------
subst_exp :: Exp -> Var -> Exp ->  Exp
---------------------------------------
-- subst_exp e1 x e2 = error "TODO: FILL THIS IN"
subst_exp e1 x e2 = case e2 of (Var s)  -> e1
                                  -- | s==(getString x)  -> e1
                                  -- | otherwise -> e2
                               (Num _)    -> e2
                               (Plus es)  -> Plus  $ map (subst_exp e1 x) es
                               (Minus es) -> Minus $ map (subst_exp e1 x) es
                               (Times es) -> Times $ map (subst_exp e1 x) es
                     where
                      getString (Var s') = s'

-------------------------------------------
test :: IO ()
-------------------------------------------
test = do
    let res = subst_exp (Var "asd") (Var "x") (Var "x")
    putStr $ "Add your tests here: " ++ (show res)
    return ()
