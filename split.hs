{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall #-}
import Text.Printf (printf)
import Data.List (isPrefixOf)

main :: IO ()
main = do
  s <- drop 3 . lines <$> getContents
  go 0 [] s
  where
    emit :: Int -> [String] -> IO ()
    emit emitted seen = do
      let module_ = "lambda" ++ printf "%02d" emitted
      writeFile (module_ ++ ".agda") $
        unlines ([ "-- ***", "", "module " ++ module_ ++ " where" ] ++ reverse seen)

    go :: Int -> [String] -> [String] -> IO ()
    go emitted seen = \case
      [] -> emit emitted seen
      "-- SPLIT" : remaining -> do
        emit emitted seen
        go (emitted + 1) seen remaining
      l : remaining | "-- SPLIT " `isPrefixOf` l -> do
        emit emitted (("-- " ++ drop (length "-- SPLIT ") l) : seen)
        go (emitted + 1) seen remaining
      line : remaining -> go emitted (line : seen) remaining

