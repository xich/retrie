-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
module Main (main) where

import Control.Exception
import Test.HUnit
import Test.Tasty
import Test.Tasty.Providers
import Test.Tasty.Runners (Result(..))

import qualified GHC.Paths as GHC.Paths
import Retrie
import AllTests
import Util (SkipTest(..))

main :: IO ()
main = allTests GHC.Paths.libdir Silent >>= defaultMain . toTasty . TestLabel "retrie"

toTasty :: Test -> TestTree
toTasty (TestLabel lbl (TestCase io)) = singleTest lbl (SkippableCase io)
toTasty (TestLabel lbl (TestList ts)) = testGroup lbl (map toTasty ts)
toTasty t = error $ "toTasty: unlabeled test " ++ show t

-- | Like tasty-hunit's 'testCase', but a 'SkipTest' exception reports the test
-- as SKIPPED (which does not fail the run) instead of failing it.
newtype SkippableCase = SkippableCase Assertion

instance IsTest SkippableCase where
  run _ (SkippableCase io) _ = do
    r <- try io
    return $ case r of
      Left (SkipTest why) -> (testPassed why) { resultShortDescription = "SKIPPED" }
      Right () -> testPassed ""
  testOptions = return []
