module Main where
import qualified Horn.Bindings.Z3          as HZ3
import qualified Horn.VCGen.VCGen as VCGen
import qualified Horn.Logic.Clauses        as HC
import qualified Horn.Nano.Nano        as Nano
import qualified Horn.Logic.Clauses as Logic
import           Z3.Monad
import System.Exit  
import Horn.CmdLine                    

----------------------------------------
resultExit :: [Bool] -> ExitCode
----------------------------------------
resultExit rs 
    | and rs = ExitSuccess
resultExit _ = ExitFailure 1

main :: IO ()
main = do
    cfg <-  getOpts  
    rs <- mapM VCGen.verifyFile $ Nano.files cfg
    exitWith (resultExit rs)
