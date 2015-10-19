{-# OPTIONS_GHC -fno-warn-orphans #-}
module Futhark.Representation.AST.Attributes.ReshapeTests
       ( tests
       )
       where

import Control.Applicative

import Test.HUnit hiding (Test)
import Test.Framework
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

import Prelude

import Futhark.Representation.AST.Attributes.Reshape
import Futhark.Representation.AST.Syntax

tests :: [Test]
tests = fuseReshapeTests ++
        informReshapeTests ++
        reshapeOuterTests ++
        reshapeInnerTests ++
        [ fuseReshapeProp
        , informReshapeProp
        ]

fuseReshapeTests :: [Test]
fuseReshapeTests =
  [ testCase (unwords ["fuseReshape ", show d1, show d2]) $
    fuseReshape (d1 :: ShapeChange Int) d2 @?= dres -- type signature to avoid warning
  | (d1, d2, dres) <- [ ([DimCoercion 1], [DimNew 1], [DimCoercion 1])
                      , ([DimNew 1], [DimCoercion 1], [DimNew 1])
                      , ([DimCoercion 1, DimNew 2], [DimNew 1, DimNew 2], [DimCoercion 1, DimNew 2])
                      , ([DimNew 1, DimNew 2], [DimCoercion 1, DimNew 2], [DimNew 1, DimNew 2])
                      ]
  ]

informReshapeTests :: [Test]
informReshapeTests =
  [ testCase (unwords ["informReshape ", show shape, show sc, show sc_res]) $
    informReshape (shape :: [Int]) sc @?= sc_res -- type signature to avoid warning
  | (shape, sc, sc_res) <-
    [ ([1, 2], [DimNew 1, DimNew 3], [DimCoercion 1, DimNew 3])
    , ([2, 2], [DimNew 1, DimNew 3], [DimNew 1, DimNew 3])
    ]
  ]

reshapeOuterTests :: [Test]
reshapeOuterTests =
  [ testCase (unwords ["reshapeOuter", show sc, show n, show shape, "==", show sc_res]) $
    reshapeOuter (intShapeChange sc) n (intShape shape) @?= (intShapeChange sc_res)
  | (sc, n, shape, sc_res) <-
    [ ([DimNew 1], 1, [4, 3], [DimNew 1, DimCoercion 3])
    , ([DimNew 1], 2, [4, 3], [DimNew 1])
    , ([DimNew 2, DimNew 2], 1, [4, 3], [DimNew 2, DimNew 2, DimNew 3])
    , ([DimNew 2, DimNew 2], 2, [4, 3], [DimNew 2, DimNew 2])
    ]
  ]

reshapeInnerTests :: [Test]
reshapeInnerTests =
  [ testCase (unwords ["reshapeInner", show sc, show n, show shape, "==", show sc_res]) $
    reshapeInner (intShapeChange sc) n (intShape shape) @?= (intShapeChange sc_res)
  | (sc, n, shape, sc_res) <-
    [ ([DimNew 1], 1, [4, 3], [DimCoercion 4, DimNew 1])
    , ([DimNew 1], 0, [4, 3], [DimNew 1])
    , ([DimNew 2, DimNew 2], 1, [4, 3], [DimNew 4, DimNew 2, DimNew 2])
    , ([DimNew 2, DimNew 2], 0, [4, 3], [DimNew 2, DimNew 2])
    ]
  ]

intShape :: [Int] -> Shape
intShape = Shape . map (Constant . IntVal . fromIntegral)

intShapeChange :: ShapeChange Int -> ShapeChange SubExp
intShapeChange = map (fmap $ Constant . IntVal . fromIntegral)

fuseReshapeProp :: Test
fuseReshapeProp = testProperty "fuseReshape result matches second argument" prop
  where prop :: ShapeChange Int -> ShapeChange Int -> Bool
        prop sc1 sc2 = map newDim (fuseReshape sc1 sc2) == map newDim sc2

informReshapeProp :: Test
informReshapeProp = testProperty "informReshape result matches second argument" prop
  where prop :: [Int] -> ShapeChange Int -> Bool
        prop sc1 sc2 = map newDim (informReshape sc1 sc2) == map newDim sc2

instance Arbitrary d => Arbitrary (DimChange d) where
  arbitrary = oneof [ DimNew <$> arbitrary
                    , DimCoercion <$> arbitrary
                    ]
