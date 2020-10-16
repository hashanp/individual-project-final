{-# OPTIONS_GHC -fplugin=Linearity.Plugin.Solver #-}

--import Storage
import Arrays (example6)
import Sessions (example9)
import Storage
import Files
import Control.Exception.Base (handle, Exception, SomeException)
import System.Random (mkStdGen, setStdGen)

main = handle m $ do
  --setStdGen (mkStdGen 40)
  example6
  example9
  putStrLn "Hi"

m :: SomeException -> IO ()
m e = do
  print "here"
  print e