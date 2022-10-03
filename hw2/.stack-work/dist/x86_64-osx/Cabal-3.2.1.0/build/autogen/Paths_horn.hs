{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_horn (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/panrui/Desktop/hw2/.stack-work/install/x86_64-osx/074b9af4dfd077748b6f41870dc6eebdbec2e374d6098ae90037b9a533339fb8/8.10.4/bin"
libdir     = "/Users/panrui/Desktop/hw2/.stack-work/install/x86_64-osx/074b9af4dfd077748b6f41870dc6eebdbec2e374d6098ae90037b9a533339fb8/8.10.4/lib/x86_64-osx-ghc-8.10.4/horn-0.1.0.0-922e84b3uMg6rLzR9IH1wU"
dynlibdir  = "/Users/panrui/Desktop/hw2/.stack-work/install/x86_64-osx/074b9af4dfd077748b6f41870dc6eebdbec2e374d6098ae90037b9a533339fb8/8.10.4/lib/x86_64-osx-ghc-8.10.4"
datadir    = "/Users/panrui/Desktop/hw2/.stack-work/install/x86_64-osx/074b9af4dfd077748b6f41870dc6eebdbec2e374d6098ae90037b9a533339fb8/8.10.4/share/x86_64-osx-ghc-8.10.4/horn-0.1.0.0"
libexecdir = "/Users/panrui/Desktop/hw2/.stack-work/install/x86_64-osx/074b9af4dfd077748b6f41870dc6eebdbec2e374d6098ae90037b9a533339fb8/8.10.4/libexec/x86_64-osx-ghc-8.10.4/horn-0.1.0.0"
sysconfdir = "/Users/panrui/Desktop/hw2/.stack-work/install/x86_64-osx/074b9af4dfd077748b6f41870dc6eebdbec2e374d6098ae90037b9a533339fb8/8.10.4/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "horn_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "horn_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "horn_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "horn_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "horn_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "horn_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
