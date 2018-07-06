#!/usr/bin/env stack
-- stack --resolver lts-11 --install-ghc runghc --package yaml --package lens --package directory
{-# LANGUAGE DeriveGeneric #-}

import Control.Monad
import Control.Lens
import Data.Char
import GHC.Generics
import Data.Map as M
import Data.List as L
import Data.Maybe
import Data.Either
import Data.Yaml
import System.Directory
import Text.Printf
data Accum = Accum Double Double Int
    deriving Generic

data Profile = Profile
    { sums :: Map String [Accum]
    , stats :: Map String [Map String String] }
    deriving Generic

instance FromJSON Profile
instance ToJSON Profile
instance FromJSON Accum
instance ToJSON Accum

accum x (Accum mean_ m2 n) = Accum mean' m2' n'
      where
        n'     = n + 1
        mean'  = (fromIntegral n * mean_ + x) / (fromIntegral $ n + 1)
        delta  = x - mean_
        m2'    = m2 + delta * delta * fromIntegral n / (fromIntegral $ n + 1)

def = Profile M.empty M.empty

mkProfile m = Profile m (M.map (L.map stat) m)
    where
      stat (Accum mean_ m2 n) = M.fromList [("mean", printf "%.03f" mean_)
                                           ,("stdev",printf "%.03f" $ sqrt $ m2 / fromIntegral n)
                                           ,("var",  printf "%.03f" $ m2 / fromIntegral n)]

main = do
    let filename = "profile_stats.yaml"
    b <- doesFileExist filename
    Profile m _ <- if b then
      fromRight def <$> decodeFileEither filename
      else return def
    v <- getLine
    print v
    -- ln <- getLine
    -- print ln
    -- unless (L.null ln) $ fail "expecting empty line"
    xs <- replicateM 3 $ do
        x <- getLine
        let y = takeWhile (\x -> isDigit x || x == '.') $ dropWhile (not . isDigit) x
        print y
        return (read y :: Double)

    let m' = m & at v %~ Just . zipWith accum xs . fromMaybe (repeat $ Accum 0 0 0)
    encodeFile filename $ mkProfile m'
