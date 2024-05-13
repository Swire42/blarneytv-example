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

import Control.Arrow ((***))

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

type Vec = V.SVec

-- | Half adder taking two bits and returning a tuple with the carry bit first
--   and the sum second
halfAdder :: Bit 1 -> Bit 1 -> (Bit 1, Bit 1)
halfAdder a b = (a .&. b, a .^. b)

halfAdder' :: (Bit 1, Bit 1) -> (Bit 1, Bit 1)
halfAdder' (a, b) = halfAdder a b

-- | Full adder taking two bits and an input carry and returning a tuple with
--   the output carry bit first and the sum second
fullAdder :: Bit 1 -> Bit 1 -> Bit 1 -> (Bit 1, Bit 1)
fullAdder a b cIn = (cOut, s1)
  where (c0, s0) = halfAdder a b
        (c1, s1) = halfAdder s0 cIn
        cOut = c0 .|. c1

fullAdder' :: (Bit 1, (Bit 1, Bit 1)) -> (Bit 1, Bit 1)
fullAdder' (cIn, (a, b)) = (sum, cOut)
  where (cOut, sum) = fullAdder a b cIn

fullAdder'' :: Bit 1 -> (Bit 1, Bit 1) -> (Bit 1, Bit 1)
fullAdder'' cIn (a, b) = (cOut, sum)
  where (cOut, sum) = fullAdder a b cIn

-- | Bit-list adder
listAdder :: Bit 1 -> [Bit 1] -> [Bit 1] -> [Bit 1]
listAdder c_in _ [] = []
listAdder c_in [] _ = []
listAdder c_in (a:as) (b:bs) =
    sum : listAdder c_out as bs
  where
    (c_out, sum) = fullAdder a b c_in

-- | Bit-vector adder
adder :: KnownNat n => Bit n -> Bit n -> Bit n
adder x y = fromBitList $ listAdder 0 (toBitList x) (toBitList y)

-- | N-bit bugged adder
doom_adder :: KnownNat n => Bit n -> Bit n -> Bit n
doom_adder x y = fromBitList $ listAdder 1 (toBitList x) (toBitList y)

-- | Adder property
prop_add :: KnownNat n => (Bit n -> Bit n -> Bit n) -> Bit n -> Bit n
                       -> Action ()
prop_add adder_imp x y = assert (adder_imp x y .==. x + y)
                                "Adder equivalent to blarney '+' operator"

--------------------------------------------------------------------------------

-- | Sequential full adder
adderSeq x y = res
  where c_in = delay 0 c_out
        res@(c_out, _) = fullAdder x y c_in

adderSeq' :: (Bit 1, Bit 1) -> (Bit 1, Bit 1)
adderSeq' (a, b) = adderSeq a b

doom_adderSeq x y = res
  where c_in = delay 0 s
        res@(c_out, s) = fullAdder x y c_in
-- | prop
prop_addSeq x y = assert (adderSeq x y === adderSeq x y)
                         "Sequential adder equivalent to itself"
prop_brokenAddSeq x y = assert (adderSeq x y === doom_adderSeq x y)
                               "Broken seq adder is equivalent to working one"

--------------------------------------------------------------------------------

delayN :: Int -> Bit 1 -> Bit 1 -> Bit 1
delayN 0 init inp = inp
delayN n init inp = out
  where
    out  = delay init rest
    rest = delayN (n-1) init inp

puls :: Int -> () -> Bit 1
puls n () = out
  where
    out  = delayN (n-1) 0 last
    last = delay 1 out

rowSeq :: ((Bit 1, a) -> (b, Bit 1)) -> (a -> b)
rowSeq circ inp = out
  where
    carryIn         = delay 0 carryOut
    (out, carryOut) = circ (carryIn, inp)

rowSeqReset :: ((Bit 1, a) -> (b, Bit 1)) -> ((Bit 1, a) -> b)
rowSeqReset circ (reset,inp) = out
  where
    carryIn         = delay 0 carry
    carry           = reset ? (0, carryOut)
    (out, carryOut) = circ (carryIn, inp)

rowSeqPeriod :: Int -> ((Bit 1, a) -> (b, Bit 1)) -> (a -> b)
rowSeqPeriod n circ inp = out
  where
    reset = puls n ()
    out   = rowSeqReset circ (reset, inp)


-- N-bit sequential adder
adderSeqN :: Int -> (Bit 1, Bit 1) -> Bit 1
adderSeqN n = rowSeqPeriod n fullAdder'

-- N-bit sequential adder
adderSeqUnroll :: forall n. KnownNat n => Vec n (Bit 1) -> Vec n (Bit 1) -> Vec n (Bit 1)
adderSeqUnroll a b = (V.unroll @n $ adderSeqN (valueOf @n)) $ V.zip a b

adderSeqUnrollBit :: forall n. KnownNat n => Bit n -> Bit n -> Bit n
adderSeqUnrollBit a b = itranspose $ adderSeqUnroll @n (itranspose a) (itranspose b)

replace pos newVal list = take pos list ++ newVal : drop (pos+1) list

adderSeqUnrollSlowdown :: forall m. KnownNat m => Int -> Vec m (Bit 1, Bit 1) -> Vec m (Bit 1)
adderSeqUnrollSlowdown n = V.unroll $ slowdown (valueOf @m) $ adderSeqN n

test1 :: Bit 1 -> Bit 1 -> Bit 1
test1 a0 b0 = s0
  where
    (c1, s0) = fullAdder a0 b0 c0
    c0 = 0

test2 :: Bit 2 -> Bit 2 -> Bit 2
test2 a b = fromBitList [s0, s1]
  where
    [a0, a1] = toBitList a
    [b0, b1] = toBitList b
    (c1, s0) = fullAdder a0 b0 c0
    (c2, s1) = fullAdder a1 b1 c1
    c0 = 0

test3 :: Bit 2 -> Bit 2 -> Bit 2
test3 a b = fromBitList [s0, s1]
  where
    [a0, a1] = toBitList a
    [b0, b1] = toBitList b
    (c1, s0) = fullAdder a0 b0 c0
    (c2, s1) = fullAdder a1 b1 c1
    c0 = delay 0 0

test4 :: Bit 2 -> Bit 2 -> Bit 2
test4 a b = fromBitList [out0, out1]
  where
    [a0, a1] = toBitList a
    [b0, b1] = toBitList b
    (out0, cOut0) = fullAdder' (cIn0, (a0, b0))
    (out1, cOut1) = fullAdder' (cIn1, (a1, b1))
    cNext0       = reset0 ? (0, cOut0)
    cNext1       = reset1 ? (0, cOut1)
    cIn0         = delay 0 cNext1
    cIn1         = cNext0
    reset0 = delay 0 tmp1
    reset1 = tmp0
    tmp0 = delay 1 reset1
    tmp1 = reset0

test_seq :: (Bit 1, Bit 1) -> (Bit 1, Bit 1) -> (Bit 1, Bit 1)
test_seq (a0, a1) (b0, b1) = (out0, out1)
  where
    (out0, cOut0) = fullAdder' (cIn0, (a0, b0))
    (out1, cOut1) = fullAdder' (cIn1, (a1, b1))
    cNext0       = reset0 ? (0, cOut0)
    cNext1       = reset1 ? (0, cOut1)
    cIn0         = delay 0 cNext1
    cIn1         = cNext0
    reset0 = delay 0 reset0
    reset1 = delay 1 reset1

test_comb :: (Bit 1, Bit 1) -> (Bit 1, Bit 1) -> (Bit 1, Bit 1)
test_comb (a0, a1) (b0, b1) = (out0, out1)
  where
    (out0, cOut0) = fullAdder' (0, (a0, b0))
    (out1, cOut1) = fullAdder' (cOut0, (a1, b1))

test5 :: Bit 2 -> Bit 2 -> Bit 2
test5 a b = fromBitList [out0, out1]
  where
    [a0, a1] = toBitList a
    [b0, b1] = toBitList b
    (out0, cOut0) = fullAdder' (cIn0, (a0, b0))
    (out1, cOut1) = fullAdder' (cIn1, (a1, b1))
    cNext0       = reset0 ? (0, cOut0)
    cNext1       = reset1 ? (1, 0)
    cIn0         = delay 0 cNext1
    cIn1         = cNext0
    reset0 = cst0 ()
    reset1 = cst0 ()

cst0 :: () -> Bit 1
cst0 () = let x = delay 0 x in x

test6 :: Int -> () -> Bit 1
test6 0 () = let x = delay 0 x .^. (delay 0 $ delay 0 x) in x
test6 n () = ((test6 (n-1) ()) ? (test6 (n-1) (), test6 (n-1) ()))

--adderSeq x y = s
--  where cIn = delay 0 cOut
--        (cOut, s) = fullAdder x y cIn
--    reset = puls n ()
--    cIn         = delay 0 cNext
--    cNext       = reset ? (0, cOut)
--    (out, cOut) = fullAdder (cIn, (a, b))

notId :: Bit 1 -> Bit 1
notId x = s
  where
    s = x .^. c
    p = delay 0 $ delay 1 p
    c = delay 0 (p .&. s)

adderSeqTVec :: forall n. (KnownNat n, 1 <= n) => TVec.TVec n (Bit 1) -> TVec.TVec n (Bit 1) -> TVec.TVec n (Bit 1)
adderSeqTVec a b = fst $ TVec.unzip $ TVec.scanReset (\(_, cIn) (a, b) -> fullAdder' (cIn, (a, b))) (TVec.replicate (0, 0)) $ TVec.zip a b

adderDelaySeqTVecBit :: forall n. (KnownNat n, 1 <= n) => Bit n -> Bit n -> Bit n
adderDelaySeqTVecBit a b = itranspose . TVec.collect (V.replicate 0) $ adderSeqTVec @n (TVec.sweep $ itranspose a) (TVec.sweep $ itranspose b)

-----

adderBatch :: (KnownNat n, 1 <= n) => B.Batch n (Bit 1, Bit 1) -> B.Batch n (Bit 1)
adderBatch = B.scanReset fullAdder'' (B.wrap 0)

adderBatchUnroll :: forall n. (KnownNat n, 1 <= n) => Vec n (Bit 1) -> Vec n (Bit 1) -> Vec n (Bit 1)
adderBatchUnroll a b = B.unroll adderBatch (V.zip a b)

adderBatchUnrollBit :: forall n. (KnownNat n, 1 <= n) => Bit n -> Bit n -> Bit n
adderBatchUnrollBit a b = itranspose $ adderBatchUnroll @n (itranspose a) (itranspose b)

adderDelayRapid :: forall n. (KnownNat n, 1 <= n) => Vec n (Bit 1) -> Vec n (Bit 1) -> Vec n (Bit 1)
adderDelayRapid a b = R.collect zero $ R.clkMul (adderBatch @n) (R.sweep $ V.zip a b)

adderDelayRapidBit :: forall n. (KnownNat n, 1 <= n) => Bit n -> Bit n -> Bit n
adderDelayRapidBit a b = itranspose $ adderDelayRapid @n (itranspose a) (itranspose b)

stateSize :: (Bits a, Bits b, KnownNat (SizeOf a)) => (a -> b) -> Int
stateSize circ = sum $ fix $ aux rootBV IntSet.empty
 where
  rootBV :: BV = toBV . pack $ circ $ unpack zero
  rootID = bvInstId rootBV

  aux :: BV -> IntSet -> IntMap Int -> IntMap Int
  aux BV{bvPrim=prim, bvInputs=inputs, bvInstId=instId} iset imap =
    if instId `IntSet.member` iset
      then IntMap.empty
      else
        IntMap.unions $ IntMap.singleton instId (
          case prim of
            Register initVal w -> w
            _ -> 0
        ) : map (\x -> aux x (IntSet.insert instId iset) imap) inputs

main :: IO ()
main = do
  -- path to script output directory
  cwd <- getCurrentDirectory
  let smtDir = cwd ++ "/Check"
  -- generate smt2 scripts
  --writeSMTScript cnfWrite (\x -> assert ((notId x) === x) "notId === id") "prop" smtDir
  --writeSMTScript cnfWrite (\x y -> assert (((delay 0 $ adderSeqUnrollBit @2 x y) === (delay 0 $ x + y))) "Inner") "inner" smtDir

  verifyDefault (Info, vconfQuiet) (\x y -> assert (((test_comb x y) === (test_seq x y))) "test_comb === test_seq")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_seq === test_seq")
  verifyDefault (Info, vconfQuiet) (\x y -> assert ((((delay 0 *** delay 0) $ test_comb x y) === ((delay 0 *** delay 0) $ test_seq x y))) "delay . test_comb === delay . test_seq")
  verifyDefault (Info, vconfQuiet) (\x -> assert ((notId x) === x) "notId === id")
  verifyDefault (Info, vconfQuiet) (assert (((delay 0 (test6 2 ())) === (delay 0 (test6 2 ())))) "test6: inner delays")
  verifyDefault (Info, vconfQuiet) (assert (((delay 0 (test6 2 ())) === (delay 0 (test6 2 ())))) "test6: inner delays")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (((delay 0 (test4 x y)) === (delay 0 (x + y)))) "test4: inner delays")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (adder @16 x y === x + y) "adder === +")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (adderSeqUnrollBit @16 x y === x + y) "adderSeqUnrollBit === +")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (adderDelaySeqTVecBit @2 x y === (delay 0 (x + y))) "adderDelaySeqTVecBit === delay . +")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (adderBatchUnrollBit @16 x y === x + y) "adderBatchUnrollBit === +")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (adderDelayRapidBit @2 x y === (delay 0 (x + y))) "adderDelayRapidBit === + (2)")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (adderDelayRapidBit @3 x y === (delay 0 (x + y))) "adderDelayRapidBit === + (3)")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (adderDelayRapidBit @16 x y === (delay 0 (x + y))) "adderDelayRapidBit === + (64)")
  verifyDefault (Info, vconfQuiet) (\x y -> assert ((test2 x y) === (x + y)) "test2: no delays")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (delay 1 ((test2 x y) === (x + y))) "test2: outer delay")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (((delay 0 (test2 x y)) === (delay 0 (x + y)))) "test2: inner delays")
  verifyDefault (Info, vconfQuiet) (\x y -> assert ((adderSeqUnrollBit @2 x y) === (x + y)) "asu: no delays")
  verifyDefault (Info, vconfQuiet) (\x y -> assert (delay 1 ((adderSeqUnrollBit @2 x y) === (x + y))) "asu: outer delay")
  verifyDefault (Info, vconfQuiet) (\x y -> assert ((delay 0 (adderSeqUnrollBit @2 x y)) === (delay 0 (x + y))) "asu: inner delays")
  verifyDefault (Info, vconfQuiet) (\x y -> assert ((adderSeqUnrollBit @2 x y) === (x + y)) "asu === +")
  verifyDefault (Info, vconfQuiet) (\x y -> assert ((delay 0 $ x + y) === adderDelaySeqTVecBit @2 x y) "d.+ === astv")
  verifyDefault (Info, vconfQuiet) (\x y -> assert ((delay 0 $ adderSeqUnrollBit @2 x y) === adderDelaySeqTVecBit @2 x y) "d.asu === astv")
  verifyDefault (Info, vconfQuiet) (\x -> assert ((adderSeqUnrollSlowdown @2 2 x) === (V.map (adderSeqN 2) x)) "unroll . slowdown === map")
  where
    cnfEasy = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }
    cnfHard = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = True, userConfIncreasePeriod = 4 } }
    cnfWrite = dfltVerifyConf { verifyConfMode = Induction (fixedDepth 2) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }
    f x = V.zipWith (===) (adderSeqUnrollSlowdown @2 2 x) (V.map (adderSeqN 2) x)
    cnf = (Verbose, vconfDefault, iconfDefault)
