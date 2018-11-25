{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RebindableSyntax #-}

module Course.State where

import Course.Core
import qualified Prelude as P
import Course.Optional
import Course.List
import Course.Functor
import Course.Applicative
import Course.Monad
import qualified Data.Set as S

-- $setup
-- >>> import Test.QuickCheck.Function
-- >>> import Data.List(nub)
-- >>> import Test.QuickCheck
-- >>> import qualified Prelude as P(fmap)
-- >>> import Course.Core
-- >>> import Course.List
-- >>> instance Arbitrary a => Arbitrary (List a) where arbitrary = P.fmap listh arbitrary

-- A `State` is a function from a state value `s` to (a produced value `a`, and a resulting state `s`).
newtype State s a =
  State {
    runState ::
      s
      -> (a, s)
  }

-- | Run the `State` seeded with `s` and retrieve the resulting state.
--
-- prop> \(Fun _ f) s -> exec (State f) s == snd (runState (State f) s)
exec ::
  State s a
  -> s
  -> s
exec state =
  snd <$> (runState state)

-- | Run the `State` seeded with `s` and retrieve the resulting value.
--
-- prop> \(Fun _ f) s -> eval (State f) s == fst (runState (State f) s)
eval ::
  State s a
  -> s
  -> a
eval state =
  fst <$> (runState state)

-- | A `State` where the state also distributes into the produced value.
--
-- >>> runState get 0
-- (0,0)
get ::
  State s s
get =
  State (\x -> (x, x))

-- | A `State` where the resulting state is seeded with the given value.
--
-- >>> runState (put 1) 0
-- ((),1)
put ::
  s
  -> State s ()
put s =
  State (\_ -> ((), s))

-- | Implement the `Functor` instance for `State s`.
--
-- >>> runState ((+1) <$> State (\s -> (9, s * 2))) 3
-- (10,6)
instance Functor (State s) where
  (<$>) ::
    (a -> b)
    -> State s a
    -> State s b
  (<$>) f state =
      State newStateF
    where
      newStateF s =
        let (x, y) = runState state s
        in (f x, y)


-- | Implement the `Applicative` instance for `State s`.
--
-- >>> runState (pure 2) 0
-- (2,0)
--
-- >>> runState (pure (+1) <*> pure 0) 0
-- (1,0)
--
-- >>> import qualified Prelude as P
-- >>> runState (State (\s -> ((+3), s P.++ ["apple"])) <*> State (\s -> (7, s P.++ ["banana"]))) []
-- (10,["apple","banana"])
instance Applicative (State s) where
  pure ::
    a
    -> State s a
  pure x =
    State (\s -> (x, s))
  (<*>) ::
    State s (a -> b)
    -> State s a
    -> State s b
  (<*>) stateF stateX =
    State (\s ->
      let
        (f, s2) = runState stateF s
        (x, s3) = runState stateX s2
      in
        (f x, s3)
    )

-- | Implement the `Bind` instance for `State s`.
--
-- >>> runState ((const $ put 2) =<< put 1) 0
-- ((),2)
--
-- >>> let modify f = State (\s -> ((), f s)) in runState (modify (+1) >>= \() -> modify (*2)) 7
-- ((),16)
instance Monad (State s) where
  (=<<) ::
    (a -> State s b)
    -> State s a
    -> State s b
  (=<<) f state =
    State (\s ->
      let
        (x, s2) = runState state s
      in
        runState (f x) s2
    )

-- | Find the first element in a `List` that satisfies a given predicate.
-- It is possible that no element is found, hence an `Optional` result.
-- However, while performing the search, we sequence some `Monad` effect through.
--
-- Note the similarity of the type signature to List#find
-- where the effect appears in every return position:
--   find ::  (a ->   Bool) -> List a ->    Optional a
--   findM :: (a -> f Bool) -> List a -> f (Optional a)
--
-- >>> let p x = (\s -> (const $ pure (x == 'c')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Full 'c',3)
--
-- >>> let p x = (\s -> (const $ pure (x == 'i')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Empty,8)
findM ::
  Monad f =>
  (a -> f Bool)
  -> List a
  -> f (Optional a)
findM _ Nil = pure Empty
findM mp (x :. xs) =
  mp x >>= \predicateResult ->
  case predicateResult of
    True -> pure (Full x)
    False -> findM mp xs

-- alternative, using foldRight, probably not very efficient:
-- findM mp = foldRight foldStep (pure Empty)
--   where
--     foldStep x mOpt = mOpt >>= branchOnOption x
--     branchOnOption x Empty = mp x >>= resultOnBool x
--     branchOnOption _ (Full y) = pure (Full y)
--     resultOnBool x True = pure (Full x)
--     resultOnBool _ False = pure Empty


-- | Find the first element in a `List` that repeats.
-- It is possible that no element repeats, hence an `Optional` result.
--
-- /Tip:/ Use `findM` and `State` with a @Data.Set#Set@.
--
-- prop> \xs -> case firstRepeat xs of Empty -> let xs' = hlist xs in nub xs' == xs'; Full x -> length (filter (== x) xs) > 1
-- prop> \xs -> case firstRepeat xs of Empty -> True; Full x -> let (l, (rx :. rs)) = span (/= x) xs in let (l2, r2) = span (/= x) rs in let l3 = hlist (l ++ (rx :. Nil) ++ l2) in nub l3 == l3
firstRepeat ::
  Ord a =>
  List a
  -> Optional a
firstRepeat xs = eval (findM mp xs) S.empty
  where
    mp x =
      get >>= \existingValues ->
      let isMember = S.member x existingValues in
      if isMember
        then pure isMember
        else put (S.insert x existingValues) >>= \_ -> pure isMember

-- reads much bit nicer using `do` syntax, and the `when` function as a guard:
--  where mp x = do
--    existingValues <- get
--    let isPresent = S.member x existingValues
--        isMissing = not isPresent
--    when isMissing $ put $ S.insert x existingValues
--    pure isPresent


-- | Remove all duplicate elements in a `List`.
-- /Tip:/ Use `filtering` and `State` with a @Data.Set#Set@.
--
-- prop> \xs -> firstRepeat (distinct xs) == Empty
--
-- prop> \xs -> distinct xs == distinct (flatMap (\x -> x :. x :. Nil) xs)
distinct ::
  Ord a =>
  List a
  -> List a
distinct xs = eval (filtering mp xs) S.empty
  where
    mp x =
      get >>= \existingValues ->
      let isMember = S.member x existingValues in
      if isMember
        then pure False
        else put (S.insert x existingValues) >>= \_ -> pure True

-- also would read much bit nicer using `do` syntax, and the `when` function as a guard:
--  where mp x = do
--    existingValues <- get
--    let isMissing = not $ S.member x existingValues
--    when isMissing $ put $ S.insert x existingValues
--    pure isMissing -- ie filtering, so include in the output only if missing


-- | A happy number is a positive integer, where the sum of the square of its digits eventually reaches 1 after repetition.
-- In contrast, a sad number (not a happy number) is where the sum of the square of its digits never reaches 1
-- because it results in a recurring sequence.
--
-- /Tip:/ Use `firstRepeat` with `produce`.
--
-- /Tip:/ Use `join` to write a @square@ function.
--
-- /Tip:/ Use library functions: @Optional#contains@, @Data.Char#digitToInt@.
--
-- >>> isHappy 4
-- False
--
-- >>> isHappy 7
-- True
--
-- >>> isHappy 42
-- False
--
-- >>> isHappy 44
-- True
isHappy :: Integer -> Bool
isHappy num
  | num <= 0 = False
  | otherwise =
      let sumsOfSquares = produce sumOfSquaresOfDigits (fromInteger num)
      in contains 1 $ firstRepeat sumsOfSquares

sumOfSquaresOfDigits :: (Integral a, Show a) => a -> a
sumOfSquaresOfDigits = sumSquares . digits

digits :: (Integral a, Show a) => a -> List a
digits = (<$>) digitToIntegral . listh . show

digitToIntegral :: Integral a => Char -> a
digitToIntegral = fromInteger . toInteger . digitToInt

sumSquares :: Integral a => List a -> a
sumSquares = mySum . map square

mySum :: Integral a => List a -> a
mySum = foldLeft (+) 0

square :: Integral a => a -> a
square = join (*) -- this strikes me as being particularly opaque
