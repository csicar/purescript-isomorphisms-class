module Iso where

import Data.Array (unzip, zip)
import Data.Array as Array
import Data.Bifunctor (class Bifunctor, bimap)
import Data.Either (Either(..), either, hush, note)
import Data.Functor.Mu (Mu)
import Data.List (List)
import Data.List as List
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.String (fromCharArray, toCharArray)
import Data.Tuple (Tuple(Tuple), curry, uncurry)
import Prelude (class Functor, Unit, Void, absurd, id, map, unit, (<<<), (>>>))

class Iso a b where
  to ∷ a → b
  from ∷ b → a

instance refl ∷ Iso a a where
  to = id
  from = id

instance sym ∷ Iso a b => Iso b a where
  to = from
  from = to

instance transitive ∷ (Iso a b, Iso b c) => Iso a c where
  to = (to ∷ a → b) >>> to
  from = (from ∷ c → b) >>> from

instance prodIdent ∷ Iso (Tuple Unit a) a where
  to (Tuple unit a) = a
  from a = Tuple unit a

instance prodComm ∷ Iso (Tuple a b) (Tuple b a) where
  to (Tuple a b) = Tuple b a
  from (Tuple b a) = Tuple a b

instance prodZeroZero ∷ Iso (Tuple Void a) Void where
  to (Tuple v a) = v
  from v = Tuple v (absurd v)

instance coProdIdent ∷ Iso (Either Void a) a where
  to (Left v) = absurd v
  to (Right a) = a
  from = Right

instance coProdAssoc ∷ Iso (Either a (Either b c)) (Either (Either a b) c) where
  to   (Left a)          = Left (Left a)
  to   (Right (Left b))  = Left (Right b)
  to   (Right (Right c)) = Right c

  from (Left (Left a))   = Left a
  from (Left (Right b))  = Right (Left b)
  from (Right c) = Right (Right c)

instance coProdComm ∷ Iso (Either a b) (Either b a) where
  to = either Right Left
  from = either Right Left

instance distributive ∷ Iso (Tuple a (Either b c)) (Either (Tuple a b) (Tuple a c)) where
  to (Tuple a bc) = either (Left <<< Tuple a) (Right <<< Tuple a) bc
  from (Left (Tuple a b)) = Tuple a (Left b)
  from (Right (Tuple a c)) = Tuple a (Right c)

instance onePlusMaybe ∷ Iso (Either Unit a) (Maybe a) where
  to = hush
  from = note unit

instance onePlusOneIsTwo ∷ Iso (Either Unit Unit) Boolean where
  to (Left unit) = true
  to (Right unit) = false
  from true = Right unit
  from false = Left unit

instance expProdSum ∷ Iso (Tuple a b → c) (a → b → c) where
  to f a b = f (Tuple a b)
  from f (Tuple a b) = f a b

instance expOne ∷ Iso (Unit → a) a where
  to f = f unit
  from a _ = a

instance expZero ∷ Iso (Void → a) Unit where
  to f = unit
  from _ = absurd

instance functorCong ∷ (Functor f, Iso a b) => Iso (f a) (f b) where
  to = map to
  from = map from

instance bifunctorCongLeft ∷ (Bifunctor f, Iso a a') => Iso (f a b) (f a' b) where
  to = bimap to id
  from = bimap from id

instance bifunctorCongRight ∷ (Bifunctor f, Iso a a') => Iso (f b a) (f b a') where
  to = bimap id to
  from = bimap id from

-- contra
--profunctor

instance newtypeIso ∷ Newtype n o => Iso n o where
  to = unwrap
  from = wrap

instance arrayTuple ∷ Iso (Array (Tuple a b)) (Tuple (Array a) (Array b)) where
  to = unzip
  from = uncurry zip

instance arrayArrays ∷ Iso (Array Char) String where
  to = fromCharArray
  from = toCharArray

instance arrayList ∷ Iso (Array a) (List a) where
  to = List.fromFoldable
  from = Array.fromFoldable
