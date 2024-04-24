import System.Directory
import System.Environment

import Blarney

import Control.Arrow ((***))

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

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

main :: IO ()
main = do
  -- path to script output directory
  cwd <- getCurrentDirectory
  let smtDir = cwd ++ "/Check/"
  -- generate smt2 scripts
  --writeSMTScript cnfWrite (\x -> assert ((notId x) === x) "notId === id") "prop" smtDir
  --writeSMTScript cnfWrite (\x y -> assert (((delay 0 $ adderSeqUnrollBit @2 x y) === (delay 0 $ x + y))) "Inner") "inner" smtDir
  --writeSMTScript dfltVerifyConf { verifyConfMode = Induction (fixedDepth 2) True } (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_seq === test_seq") "slow_seqseq_2" smtDir
  --writeSMTScript dfltVerifyConf { verifyConfMode = Induction (fixedDepth 3) True } (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_seq === test_seq") "slow_seqseq_3" smtDir
  --writeSMTScript dfltVerifyConf { verifyConfMode = Induction (fixedDepth 4) True } (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_seq === test_seq") "slow_seqseq_4" smtDir
  --writeSMTScript dfltVerifyConf { verifyConfMode = Induction (fixedDepth 4) True } (\x -> (assert ((notId x) === x) "notId === id") >> (assert ((notId x) === x) "notId === id, bis")) "bis" smtDir

  --verifyWith cnfEasy (\x y -> assert (((test_comb x y) === (test_seq x y))) "test_comb === test_seq")
  --verifyWith cnfEasy (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_comb === test_comb")
  --verifyWith cnfEasy (\x y -> assert ((((delay 0 *** delay 0) $ test_comb x y) === ((delay 0 *** delay 0) $ test_seq x y))) "delay . test_comb === delay . test_seq")
  --verifyWith cnfEasy (assert (((delay 0 (test6 2 ())) === (delay 0 (test6 2 ())))) "test6: inner delays")
  --verifyWith cnfEasy (\x y -> assert (((delay 0 (test4 x y)) === (delay 0 (x + y)))) "test4: inner delays")
  --verifyWith cnfEasy (\x -> (assert ((notId x) === x) "notId === id"))
  --verifyWith cnfEasy (\x -> (assert ((notId x) === x) "notId === id") >> (assert ((notId x) === x) "notId === id, bis"))
  --verifyWith cnfEasy (\x y -> assert (adder @16 x y === x + y) "adder === +")
  --assertBoundedWhole write_screen 3
  --verifyFixed VerifConf { restrictedStates = True, write = write_screen } (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_comb === test_seq") "sm"
  --verifyOfflineFixed (verb, VerifConf { restrictedStates = True, write = write_nothing, giveModel = True }, FixedConf { depth = 4 }) (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_seq === test_seq") "a" "Check"
  --verifyLiveFixed (verb, vconfDefault, fconfCombinational) (\(x :: Bit 1) (y :: Bit 1) -> assert ((inv (x .|. y)) === ((inv x) .&. (inv y))) "De Morgan")
  --verifyLiveIncremental cnfNew (assert (dontCare === (dontCare :: Bit 1)) "don't care === 0")
  --verifyLiveFixed (verb, VerifConf { restrictedStates = True, write = write_nothing, giveModel = True }, FixedConf { depth = 4 }) (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_seq === test_seq")
  --verifyLiveIncremental cnfNew (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_seq === test_seq")
  --verifyLiveIncremental cnfNew (\x -> assert (((notId x) === (id x))) "notId === id")
  where
    cnfEasy = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }
    cnfHard = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = True, userConfIncreasePeriod = 4 } }
    cnfWrite = dfltVerifyConf { verifyConfMode = Induction (fixedDepth 3) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }

    --verb = Verbose
    --cnfNew = (verb, vconfDefault, iconfDefault)
