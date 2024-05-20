{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger      #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

import System.Directory
import System.Environment

import Blarney
import qualified Blarney.SList as SList
import qualified Blarney.SVec as V
import qualified Blarney.TVec as TVec
import qualified Blarney.Batch as B
import qualified Blarney.FakeRapid as R
import Blarney.Retime
import Blarney.ITranspose
import Blarney.Nat

import Data.Tuple
import Control.Arrow ((***))

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

type Vec = V.SVec
type B1 = Bit 1

-- | Half adder taking two bits and returning a tuple with the carry bit first
--   and the sum second
halfAdder :: B1 -> B1 -> (B1, B1)
halfAdder a b = (a .&. b, a .^. b)

-- | Full adder taking two bits and an input carry and returning a tuple with
--   the output carry bit first and the sum second
fullAdder :: B1 -> B1 -> B1 -> (B1, B1)
fullAdder cIn a b = (s1, cOut)
  where (c0, s0) = halfAdder a b
        (c1, s1) = halfAdder s0 cIn
        cOut = c0 .|. c1

builtinAdder :: forall n. KnownNat n => Vec n B1 -> Vec n B1 -> Vec n B1
builtinAdder a b = itranspose $ (itranspose a :: Bit n) + (itranspose b :: Bit n)

rippleAdder :: forall n. KnownNat n => B1 -> Vec n B1 -> Vec n B1 -> (Vec n B1, B1)
rippleAdder cIn a b = ifZero @n (V.empty, cIn) (aux cIn a b)
  where
    aux :: forall n. (KnownNat n, 1 <= n) => B1 -> Vec n B1 -> Vec n B1 -> (Vec n B1, B1)
    aux cIn a b = (s, cOut)
      where
        (a1, at) = V.uncons a
        (b1, bt) = V.uncons b
        (s1, c1) = fullAdder cIn a1 b1
        (st, cOut) = rippleAdder c1 at bt
        s = V.cons s1 st

rippleAdderSimple :: KnownNat n => Vec n B1 -> Vec n B1 -> Vec n B1
rippleAdderSimple a b = fst $ rippleAdder zero a b

-----

-- batch adder built using a single fulladder
batchAdder :: (KnownNat n, 1 <= n) => B.Batch n (B1, B1) -> B.Batch n (B1)
batchAdder = B.scanReset kernel (B.wrap 0)
  where kernel cIn (a, b) = let (s, cOut) = fullAdder cIn a b in (cOut, s)

-- unrolled version
batchAdderUnroll :: forall n. (KnownNat n, 1 <= n) => Vec n (B1) -> Vec n (B1) -> Vec n (B1)
batchAdderUnroll a b = B.unroll batchAdder (V.zip a b)

-- sweep/collect version
rapidAdderDelayed :: forall n. (KnownNat n, 1 <= n) => Vec n (B1) -> Vec n (B1) -> Vec n (B1)
rapidAdderDelayed a b = R.collect zero $ R.clkMul (batchAdder @n) (R.sweep $ V.zip a b)

-----

-- n*m-adder built using a single fast m-adder
lpgsAdderDelayed :: forall n m. (KnownNat n, 1 <= n, KnownNat m) => Vec (n*m) B1 -> Vec (n*m) B1 -> Vec (n*m) B1
lpgsAdderDelayed a b = castOut $ R.clkMul aux $ castIn a b
  where
    castIn a b = R.sweep $ V.zip (V.unconcat @n @m a) (V.unconcat @n @m b)
    castOut s = V.concat $ R.collect zero s
    aux :: B.Batch n (Vec m B1, Vec m B1) -> B.Batch n (Vec m B1)
    aux = B.scanReset kernel (B.wrap 0)
    kernel cIn (a, b) = let (s, cOut) = rippleAdder cIn a b in (cOut, s)

-----

pair2vec :: (a, a) -> Vec 2 a
pair2vec (x1, x2) = V.cons x1 $ V.singleton x2
vec2pair :: Vec 2 a -> (a, a)
vec2pair xs = (V.head xs, V.last xs)

evens :: forall n a b. KnownNat n => ((a, a) -> (b, b)) -> Vec (2*n) a -> Vec (2*n) b
evens f = V.concat . V.map (pair2vec . f . vec2pair) . V.unconcat @n @2

parl :: forall n a b. KnownNat n => (Vec n a -> Vec n b) -> (Vec n a -> Vec n b) -> Vec (2*n) a -> Vec (2*n) b
parl f g xs = V.append (f $ V.take xs) (g $ V.drop @(2*n) @n xs)

two :: forall n a b. KnownNat n => (Vec n a -> Vec n b) -> Vec (2*n) a -> Vec (2*n) b
two f = parl f f

riffle :: forall n a. KnownNat n => Vec (2*n) a -> Vec (2*n) a
riffle = V.concat @n @2 . itranspose . V.unconcat @2 @n

unriffle :: forall n a. KnownNat n => Vec (2*n) a -> Vec (2*n) a
unriffle = V.concat @2 @n . itranspose . V.unconcat @n @2

ilv :: forall n a b. KnownNat n => (Vec n a -> Vec n b) -> Vec (2*n) a -> Vec (2*n) b
ilv f = riffle . two f . unriffle

bfly :: forall n a. KnownNat n => ((a, a) -> (a, a)) -> Vec (2^n) a -> Vec (2^n) a
bfly f = ifZero @n id aux
  where
    aux :: (1 <= n) => Vec (2^n) a -> Vec (2^n) a
    aux = evens f . ilv (bfly f)

alt :: forall n a b. KnownNat n => Vec (4*n) a -> Vec (4*n) a
alt = V.concat @n @4 . V.map (parl id (evens swap)) . V.unconcat @n @4

vee :: forall n a b. KnownNat n => (Vec (2*n) a -> Vec (2*n) b) -> Vec (4*n) a -> Vec (4*n) b
vee f = alt . ilv f . alt

vfly :: forall n a. KnownNat n => ((a, a) -> (a, a)) -> Vec (2^n) a -> Vec (2^n) a
vfly f = ifZero @n id (ifZero @(n-1) (evens f) (V.forceCast . aux @(n-2) . V.forceCast))
  where
    aux :: forall m. (KnownNat m) => Vec ((2^m)*4) a -> Vec ((2^m)*4) a
    aux = evens @((2^m)*2) f . vee (vfly @(m+1) f)

que :: forall n a b. KnownNat n => (Vec (2*n) a -> Vec (2*n) b) -> Vec (4*n) a -> Vec (4*n) b
que f = ilv riffle . two f . ilv unriffle

mid :: forall n a b. (KnownNat n, 2 <= n) => (Vec (n-2) a -> Vec (n-2) a) -> Vec n a -> Vec n a
mid f xs = V.cons (V.head xs) (V.append (f $ V.init $ V.tail xs) (V.singleton $ V.last xs))

qfly :: forall n a. KnownNat n => ((a, a) -> (a, a)) -> Vec (2^n) a -> Vec (2^n) a
qfly f = ifZero @n id (ifZero @(n-1) (evens f) (V.forceCast . aux @(n-2) . V.forceCast))
  where
    aux :: forall m. (KnownNat m) => Vec ((2^m)*4) a -> Vec ((2^m)*4) a
    aux = ifZero @((2^m)*4-1) undefined $ mid (evens @((2^m)*2-1) f) . que (qfly @(m+1) f)

hrep :: Int -> (a -> a) -> (a -> a)
hrep 0 f = f
hrep n f = hrep (n-1) f . f

--

cmp :: (B1, B1) -> (B1, B1)
cmp (x, y) = (x .&. y, x .|. y)

sorted :: KnownNat n => Vec n B1 -> B1
sorted = snd . V.foldr (\x (min, sorted) -> (x .&. min, sorted .&. ((inv x) .|. min))) (1, 1)

sortB :: forall n a. KnownNat n => ((a, a) -> (a, a)) -> Vec (2^n) a -> Vec (2^n) a
sortB cmp = ifZero @n id aux
  where
    aux :: (1 <= n) => Vec (2^n) a -> Vec (2^n) a
    aux = bfly cmp . parl (sortB cmp) (sortB $ swap . cmp)

sortV :: forall n a. KnownNat n => ((a, a) -> (a, a)) -> Vec (2^n) a -> Vec (2^n) a
sortV cmp = hrep (valueOf @n) (vfly cmp)

sortQ :: forall n a. KnownNat n => ((a, a) -> (a, a)) -> Vec (2^n) a -> Vec (2^n) a
sortQ cmp = hrep (valueOf @n) (qfly cmp)

-----

sortVRapid :: forall n a. (KnownNat n, Bits a, KnownNat (SizeOf a), 1 <= n) => ((a, a) -> (a, a)) -> Vec (2^n) a -> Vec (2^n) a
sortVRapid cmp = V.last . R.collect zero . R.clkMul aux . R.replicate . B.wrap
  where
    aux :: B.Batch n (Vec (2^n) a) -> B.Batch n (Vec (2^n) a)
    aux x = ret
      where ret = (B.lift $ vfly cmp) (B.shiftReset x ret)

sortQRapid :: forall n a. (KnownNat n, Bits a, KnownNat (SizeOf a), 1 <= n) => ((a, a) -> (a, a)) -> Vec (2^n) a -> Vec (2^n) a
sortQRapid cmp = V.last . R.collect zero . R.clkMul aux . R.replicate . B.wrap
  where
    aux :: B.Batch n (Vec (2^n) a) -> B.Batch n (Vec (2^n) a)
    aux x = ret
      where ret = (B.lift $ qfly cmp) (B.shiftReset x ret)

-----

main :: IO ()
main = do
  -- path to script output directory
  cwd <- getCurrentDirectory
  let smtDir = cwd ++ "/Check"

  checkAuto Info (\x y -> assert (rippleAdderSimple @16 x y === builtinAdder x y) "rippleAdder === builtinAdder")
  checkAuto Info (\x y -> assert (batchAdderUnroll @16 x y === builtinAdder x y) "batchAdderUnrollBit === builtinAdder")
  checkAuto Info (\x y -> assert (rapidAdderDelayed @16 x y === (delay zero (builtinAdder x y))) "rapidAdderDelayedBit === builtinAdder")
  checkAuto Info (\x y -> assert (lpgsAdderDelayed @4 @4 x y === (delay zero (builtinAdder x y))) "lpgsAdderDelayed === builtinAdder")

  checkAuto Info (\x -> assert (sorted $ sortB cmp (x :: Vec 16 B1)) "sortB is sorted")
  checkAuto Info (\x -> assert (sorted $ sortV cmp (x :: Vec 16 B1)) "sortV is sorted")
  checkAuto Info (\x -> assert (sorted $ sortQ cmp (x :: Vec 16 B1)) "sortQ is sorted")
  checkAuto Info (\x -> assert (sorted $ sortVRapid cmp (x :: Vec 8 B1)) "sortVRapid is sorted")
  checkAuto Info (\x -> assert (sorted $ sortQRapid cmp (x :: Vec 8 B1)) "sortQRapid is sorted")
  checkAuto Info (\x -> assert ((sortB cmp x) === (sortV cmp (x :: Vec 8 B1))) "sortB === sortV")
  checkAuto Info (\x -> assert ((sortB cmp x) === (sortQ cmp (x :: Vec 8 B1))) "sortB === sortQ")
  checkAuto Info (\x -> assert ((delay zero $ sortV cmp x) === (sortVRapid cmp (x :: Vec 8 B1))) "delay . sortV === sortVRapid")
  checkAuto Info (\x -> assert ((delay zero $ sortV cmp x) === (sortVRapid cmp (x :: Vec 8 B1))) "delay . sortQ === sortQRapid")
