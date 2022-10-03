{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Horn.CmdLine (getOpts) where

import Horn.Nano.Nano                      (Config (..))
import System.Console.CmdArgs

---------------------------------------------------------------------------------
-- | Parsing Command Line -------------------------------------------------------
---------------------------------------------------------------------------------

config = Config { 
   files   = def &= typ "TARGET" 
                 &= args 
                 &= typFile  
 } &= verbosity
   &= program "horn" 
   &= help    "The horn Verification System" 
   &= summary "horn" 
   &= details [ "horn is suite of toy program verifiers"
              , ""
              , "To check a file foo.js, type:"
              , "  horn foo.js "
              ]

getOpts :: IO Config 
getOpts = do md <- cmdArgs config 
             putStrLn $ banner md
             return   $ md

banner args =  "horn\n" 
            ++ "horn" ++ show args ++ "\n" 