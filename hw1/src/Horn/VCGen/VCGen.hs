 {-# LANGUAGE OverloadedStrings #-}
module Horn.VCGen.VCGen where

import           Control.Monad.State.Strict
import qualified Horn.Nano.Nano as Nano
import qualified Horn.Logic.Clauses as Logic
import qualified Horn.Bindings.Z3 as Z3
import           Debug.Trace
import           Control.Monad.Trans.Class  (lift)
import           Data.Foldable (foldrM)
import           Rainbow
import Data.Function ((&))

data VCState = VCS { vc :: [Logic.Base]}
type VCM = StateT VCState IO

-----------------------------------------------------------------------------------
generateStmtVC :: Nano.Stmt -> Logic.Base -> VCM Logic.Base 
-----------------------------------------------------------------------------------
generateStmtVC (Nano.Assume phi) post = do
              let pre = Logic.Implies phi post
              return pre

generateStmtVC (Nano.Assert phi) post = do
              let pre = Logic.And [post, phi]
              return pre              

-- generateStmtVC _ _ = error "TODO: FILL THIS IN"
generateStmtVC Nano.Skip post = do
              return post

generateStmtVC (Nano.Assign x e) post = case post of
                (Logic.Tr)  -> return Logic.Tr
                (Logic.Fl)  -> return Logic.Fl
                (Logic.Eq e1 e2)  -> do
                        let e1' = Logic.subst_exp (Nano.expToBase e) (Logic.Var x) e1
                            e2' = Logic.subst_exp (Nano.expToBase e) (Logic.Var x) e2
                        return (Logic.Eq e1' e2')
                (Logic.Geq e1 e2) -> do
                        let e1' = Logic.subst_exp (Nano.expToBase e) (Logic.Var x) e1
                            e2' = Logic.subst_exp (Nano.expToBase e) (Logic.Var x) e2
                        return (Logic.Geq e1' e2')
                (Logic.Leq e1 e2) -> do
                        let e1' = Logic.subst_exp (Nano.expToBase e) (Logic.Var x) e1
                            e2' = Logic.subst_exp (Nano.expToBase e) (Logic.Var x) e2
                        return (Logic.Leq e1' e2')
                (Logic.Neg b)  -> do
                        let b' = Logic.subst (Nano.expToBase e) (Logic.Var x) b
                        return (Logic.Neg b')
                (Logic.And bs) -> do
                        let bs'= map (Logic.subst (Nano.expToBase e) (Logic.Var x)) bs
                        return (Logic.And bs')
                (Logic.Or bs)  -> do
                        let bs'= map (Logic.subst (Nano.expToBase e) (Logic.Var x)) bs
                        return (Logic.Or bs')
                (Logic.Implies b1 b2) -> do
                        let b1' = Logic.subst (Nano.expToBase e) (Logic.Var x) b1
                            b2' = Logic.subst (Nano.expToBase e) (Logic.Var x) b2
                        return (Logic.Implies b1' b2')

generateStmtVC (Nano.Seq s1 s2) post = do
        post' <- generateStmtVC s2 post
        pre <- generateStmtVC s1 post'
        return pre

generateStmtVC (Nano.SeqList ss) post = do
        --let f i = do { pre' <- () post; return i }
        pre <- foldrM generateStmtVC post ss
        return pre

generateStmtVC (Nano.If b s1 s2) post = do 
        pre <- generateStmtVC s1 post
        let imp1 = Logic.Implies (Nano.bexpToBase b) pre
            imp2 = Logic.Implies (Logic.Neg (Nano.bexpToBase b)) pre
        return (Logic.And [imp1, imp2])
       
generateStmtVC (Nano.While inv b s) post = do
        pre <- generateStmtVC s inv
        let cond1 = Logic.Implies (Logic.And [inv, Nano.bexpToBase b]) pre
            cond2 = Logic.Implies (Logic.And [inv, Logic.Neg (Nano.bexpToBase b)]) post
            vc = Logic.And [cond1, cond2]
        addVC vc
        return inv

-------------------------------------------------------------------
isValid :: Logic.Base -> IO Bool
-------------------------------------------------------------------
isValid pre = do
         b <- Z3.implies (Logic.Tr) pre
         return b

-------------------------------------------------------------------
checkVCs :: Nano.Stmt -> Logic.Base -> Logic.Base -> IO Bool
-------------------------------------------------------------------
checkVCs pgm post init = do 
        res <- runStateT (generateStmtVC pgm post) initState
        let pre = fst $ res -- WP
        let vcs = vc $ snd $ res
        sol1 <- Z3.implies init pre
        sol2 <- isValid (Logic.And vcs)
        return $ sol1 && sol2

-------------------------------------------------------------------
initState ::  VCState
-------------------------------------------------------------------
initState = VCS []

-------------------------------------------------------------------
getVCs :: VCM [Logic.Base]
-------------------------------------------------------------------
getVCs = vc <$> get

-------------------------------------------------------------------
addVC :: Logic.Base -> VCM ()
-------------------------------------------------------------------
addVC b = do
              st <- get
              let vcs = b:(vc st)
              put VCS {vc = vcs}

-------------------------------------------
verifyFile :: FilePath ->  IO (Bool)
-------------------------------------------
verifyFile f = do
        stmts <- Nano.parseNanoFromFile f
        let prog = Nano.SeqList stmts
        putStr $ "Checking the file : " ++ (show f) ++ "\n"  ++ (show prog)
        res <- checkVCs prog Logic.Tr Logic.Tr 
        printResult res
        return res

-------------------------------------------
printResult :: Bool -> IO()
-------------------------------------------
printResult True = do
        putStr $ "Verification: "
        putChunkLn $ "passed"   & fore green

printResult False = do
        putStr $ "Verification: "
        putChunkLn $ "failed"  & fore red

-------------------------------------------
test :: IO ()
-------------------------------------------
test = do
    -- res <- verifyFile "tests/pos/while5.js"    
    -- return ()

    res <- checkVCs pgm Logic.Tr Logic.Tr
    printResult res
    putStr $ "Checking the file : " ++ "\n" ++ (show pgm)
    return ()
    where

      -- a2 = Nano.Assign "x"  (Nano.Plus (Nano.Var "y") (Nano.Num 1))
      -- a1 = Nano.Assign "y"  (Nano.Num 1)
      -- pgm = Nano.SeqList [a1,a2]
      -- post = Logic.Geq (Logic.Var "x") (Logic.Num 1)
      -- init = Logic.Tr 

      -- {True} if y<=0 then x:=1 else x:=y {x > 0}
      -- cond = Nano.Lte (Nano.Var "y") (Nano.Num 0)
      -- s1 = Nano.Assign "x" (Nano.Num 1)
      -- s2 = Nano.Assign "x" (Nano.Var "y")
      -- pgm = Nano.If cond s1 s2
      -- post = Logic.Geq (Logic.Var "x") (Logic.Num 0)
      -- init = Logic.Tr 
      
      -- {x=0} while (I:=x=<6) x=<5 x=x+1 {x=6}
      cond = Nano.Lte (Nano.Var "x") (Nano.Num 5)
      s = Nano.Assign "x" (Nano.Plus (Nano.Var "x") (Nano.Num 1))
      inv = Logic.Leq (Logic.Var "x") (Logic.Num 6)
      pgm = Nano.SeqList [init, Nano.While inv cond s, post]
      
      post = Nano.Assert (Logic.Eq (Logic.Var "x") (Logic.Num 6) )
      init = Nano.Assume (Logic.Eq (Logic.Var "x") (Logic.Num 0)) 

      -- [SeqList [Assign "x" (Num 0)],While (x≤6) (Lte (Var "x") (Num 5)) (SeqList [Skip,Assign "x" (Plus (Var "x") (Num 1))]),Assert x=6]  
