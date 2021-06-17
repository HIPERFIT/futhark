{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Futhark.TypeChecker.TypesTests (tests) where

import qualified Data.Map as M
import Futhark.FreshNames
import Language.Futhark
import Language.Futhark.Semantic
import Language.Futhark.SyntaxTests ()
import Language.Futhark.TypeChecker (initialEnv)
import Language.Futhark.TypeChecker.Monad
import Language.Futhark.TypeChecker.Types
import Test.Tasty
import Test.Tasty.HUnit

evalTest :: TypeExp Name -> ([VName], StructRetType) -> TestTree
evalTest te expected =
  testCase (pretty te) $
    case fmap (extract . fst) (run (checkTypeExp te)) of
      Left e -> assertFailure $ "Failed: " <> pretty e
      Right actual ->
        actual @?= expected
  where
    extract (_, svars, t, _) = (svars, t)
    run = snd . runTypeM env mempty (mkInitialImport "") blankNameSource
    -- We hack up an environment with some predefined type
    -- abbreviations for testing.  This is all pretty sensitive to the
    -- specific unique names, so we have to be careful!
    env =
      initialEnv
        { envTypeTable =
            M.fromList
              [ ( "square_1000",
                  TypeAbbr
                    Unlifted
                    [TypeParamDim "n_1001" mempty]
                    "[n_1001][n_1001]i32"
                ),
                ( "fun_1100",
                  TypeAbbr
                    Lifted
                    [ TypeParamType Lifted "a_1101" mempty,
                      TypeParamType Lifted "b_1102" mempty
                    ]
                    "a_1101 -> b_1102"
                )
              ]
              <> envTypeTable initialEnv,
          envNameMap =
            M.fromList
              [ ((Type, "square"), "square_1000"),
                ((Type, "fun"), "fun_1100")
              ]
              <> envNameMap initialEnv
        }

tests :: TestTree
tests =
  testGroup
    "Type expression elaboration"
    [ evalTest
        "[]i32"
        ([], "?[d_0].[d_0]i32"),
      evalTest
        "[][]i32"
        ([], "?[d_0][d_1].[d_0][d_1]i32"),
      evalTest
        "bool -> []i32"
        ([], "bool -> ?[d_0].[d_0]i32"),
      evalTest
        "bool -> []f32 -> []i32"
        (["d_0"], "bool -> [d_0]f32 -> ?[d_1].[d_1]i32"),
      evalTest
        "([]i32,[]i32)"
        ([], "?[d_0][d_1].([d_0]i32, [d_1]i32)"),
      evalTest
        "{a:[]i32,b:[]i32}"
        ([], "?[d_0][d_1].{a:[d_0]i32, b:[d_1]i32}"),
      evalTest
        "?[n].[n][n]bool"
        ([], "?[n_0].[n_0][n_0]bool"),
      evalTest
        "([]i32 -> []i32) -> bool -> []i32"
        (["d_0"], "([d_0]i32 -> ?[d_1].[d_1]i32) -> bool -> ?[d_2].[d_2]i32"),
      evalTest
        "((k: i64) -> [k]i32 -> [k]i32) -> []i32 -> bool"
        (["d_1"], "((k_0: i64) -> [k_0]i32 -> [k_0]i32) -> [d_1]i32 -> bool"),
      evalTest
        "square [10]"
        ([], "[10][10]i32"),
      evalTest
        "square []"
        ([], "?[d_0].[d_0][d_0]i32"),
      evalTest
        "bool -> square []"
        ([], "bool -> ?[d_0].[d_0][d_0]i32"),
      evalTest
        "(k: i64) -> square [k]"
        ([], "(k_0: i64) -> [k_0][k_0]i32"),
      evalTest
        "fun i32 bool"
        ([], "i32 -> bool"),
      evalTest
        "fun ([]i32) bool"
        ([], "?[d_0].[d_0]i32 -> bool"),
      evalTest
        "fun bool ([]i32)"
        ([], "?[d_0].bool -> [d_0]i32"),
      evalTest
        "bool -> fun ([]i32) bool"
        ([], "bool -> ?[d_0].[d_0]i32 -> bool"),
      evalTest
        "bool -> fun bool ([]i32)"
        ([], "bool -> ?[d_0].bool -> [d_0]i32")
    ]
