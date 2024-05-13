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
twoLevelAdderDelayed :: forall n m. (KnownNat n, 1 <= n, KnownNat m) => Vec (n*m) B1 -> Vec (n*m) B1 -> Vec (n*m) B1
twoLevelAdderDelayed a b = castOut $ R.clkMul aux $ castIn a b
  where
    castIn a b = R.sweep $ V.zip (V.unconcat @n @m a) (V.unconcat @n @m b)
    castOut s = V.concat $ R.collect zero s
    aux :: B.Batch n (Vec m B1, Vec m B1) -> B.Batch n (Vec m B1)
    aux = B.scanReset kernel (B.wrap 0)
    kernel cIn (a, b) = let (s, cOut) = rippleAdder cIn a b in (cOut, s)

main :: IO ()
main = do
  -- path to script output directory
  cwd <- getCurrentDirectory
  let smtDir = cwd ++ "/Check"

  verifyDefault (Info, vconfQuiet) (\x y -> assert (rippleAdderSimple @16 x y === builtinAdder x y) "rippleAdder === builtinAdder")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (batchAdderUnroll @16 x y === builtinAdder x y) "batchAdderUnrollBit === builtinAdder")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (rapidAdderDelayed @16 x y === (delay zero (builtinAdder x y))) "rapidAdderDelayedBit === builtinAdder")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (twoLevelAdderDelayed @4 @4 x y === (delay zero (builtinAdder x y))) "twoLevelAdderDelayed === builtinAdder")
  where
    cnf = (Verbose, vconfDefault, iconfDefault)
