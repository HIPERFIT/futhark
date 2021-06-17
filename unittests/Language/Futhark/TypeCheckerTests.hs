module Language.Futhark.TypeCheckerTests (tests) where

import qualified Language.Futhark.TypeChecker.TypesTests
import Test.Tasty

tests :: TestTree
tests =
  testGroup
    "Source type checker tests"
    [ Language.Futhark.TypeChecker.TypesTests.tests
    ]
