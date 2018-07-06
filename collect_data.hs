#!/usr/bin/env stack
-- stack --resolver lts-11 --install-ghc runghc --package yaml --package lens --package directory --package erf
{-# LANGUAGE DeriveGeneric,DeriveFunctor #-}

import Data.Number.Erf
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
import System.Environment
import Text.Printf

data Accum = Accum Double Double Int
    deriving Generic

data Profile = Profile
    { sums :: Map String [Accum]
    , stats :: Map String [Map String String] }
    deriving (Generic)

instance FromJSON Profile
instance ToJSON   Profile
instance FromJSON Accum
instance ToJSON   Accum

accum x (Accum mean_ m2 n) = Accum mean' m2' n'
      where
        n'     = n + 1
        mean'  = (fromIntegral n * mean_ + x) / (fromIntegral $ n + 1)
        delta  = x - mean_
        m2'    = m2 + delta * delta * fromIntegral n / (fromIntegral $ n + 1)

def :: Profile
def = Profile M.empty M.empty

mean (Accum mean_ m2 n) = mean_

variance (Accum mean_ m2 n) = m2 / fromIntegral n

stdev (Accum mean_ m2 n) = sqrt $ m2 / fromIntegral n

mkProfile :: Map String [Accum] -> Profile
mkProfile m = Profile m (M.map (L.map stat) m)
    where
      stat a = M.fromList [("mean", printf "%.03f" $ mean a)
                          ,("stdev",printf "%.03f" $ stdev a)
                          ,("var",  printf "%.03f" $ variance a)]

-- prettify :: Profile Double -> Profile String
-- prettify = fmap (printf "%.03f")

-- toNumbers :: Profile a -> Profile Double
-- toNumbers (Profile m _) = mkProfile m

filename = "profile_stats.yaml"

testHyp = do
    Profile m _ <- readProfile
    let vA = m!"version A"
        vB = m!"version B"
    mapM_ print $ zipWith (\a b -> (normcdf $ (mean b - mean a) / sqrt (variance a + variance b) :: Double)) vA vB
    mapM_ print $ zipWith (\a b -> (normcdf $ (mean a - mean b) / sqrt (variance a + variance b) :: Double)) vA vB

readProfile = do
    b <- doesFileExist filename
    if b then
      fromRight def <$> decodeFileEither filename
      else return def


readExperiment = do
    Profile m _ <- readProfile
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

main = do
    xs <- getArgs
    if xs == ["-c"] then
      testHyp
      else readExperiment
