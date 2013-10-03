module L0C.Range (
      Range
    , empty
    , singleton
    , range
    , bounds
    , contains
    , extendTo
    , intersect
    , union
    ) where


data Range a = Empty | Bounds a a
    deriving (Eq, Ord)


empty :: Range a
empty = Empty


singleton :: a -> Range a
singleton x = Bounds x x


range :: (Ord a) => a -> a -> Range a
range l u = if l <= u
    then Bounds l u
    else Empty


bounds :: Range a -> Maybe (a, a)
bounds Empty = Nothing
bounds (Bounds l u) = Just (l, u)


contains :: (Ord a) => Range a -> a -> Bool
contains Empty _ = False
contains (Bounds l u) x = l <= x && x <= u


extendTo :: (Ord a) => Range a -> a -> Range a
extendTo Empty x = singleton x
extendTo (Bounds l u) x
    | x < l = Bounds x u
    | x > u = Bounds l x
    | otherwise = Bounds l u


intersect :: (Ord a) => Range a -> Range a -> Range a
intersect Empty _ = Empty
intersect _ Empty = Empty
intersect (Bounds l1 u1) (Bounds l2 u2) = range l u
    where
        l = max l1 l2
        u = min u1 u2


union :: (Ord a) => Range a -> Range a -> Maybe (Range a)
union Empty range = Just range
union range Empty = Just range
union b1@(Bounds l1 u1) b2@(Bounds l2 u2) = case intersect b1 b2 of
    Empty -> Nothing
    Bounds{} -> Just $ Bounds l u
    where
        l = min l1 l2
        u = max u1 u2



