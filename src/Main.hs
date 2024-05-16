import System.Directory
import System.Environment

import Blarney

import Control.Arrow ((***))

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

halfAdder :: Bit 1 -> Bit 1 -> (Bit 1, Bit 1)
halfAdder a b = (a .&. b, a .^. b)

fullAdder :: Bit 1 -> Bit 1 -> Bit 1 -> (Bit 1, Bit 1)
fullAdder a b cIn = (cOut, s1)
  where (c0, s0) = halfAdder a b
        (c1, s1) = halfAdder s0 cIn
        cOut = c0 .|. c1

adder2UnrollSeq :: (Bit 1, Bit 1) -> (Bit 1, Bit 1) -> (Bit 1, Bit 1)
adder2UnrollSeq (a0, a1) (b0, b1) = (out0, out1)
  where
    (cOut0, out0) = fullAdder a0 b0 cIn0
    (cOut1, out1) = fullAdder a1 b1 cIn1
    cNext0       = reset0 ? (0, cOut0)
    cNext1       = reset1 ? (0, cOut1)
    cIn0         = delay 0 cNext1
    cIn1         = cNext0
    reset0 = delay 0 reset0
    reset1 = delay 1 reset1

adder2Comb :: (Bit 1, Bit 1) -> (Bit 1, Bit 1) -> (Bit 1, Bit 1)
adder2Comb (a0, a1) (b0, b1) = (out0, out1)
  where
    (cOut0, out0) = fullAdder a0 b0 0
    (cOut1, out1) = fullAdder a1 b1 cOut0

ausEqAus :: (Bit 1, Bit 1) -> (Bit 1, Bit 1) -> Action ()
ausEqAus x y = assert ((adder2UnrollSeq x y) === (adder2UnrollSeq x y)) "aus === aus"

notId :: Bit 1 -> Bit 1
notId x = s
  where
    s = x .^. c
    p = delay 0 $ delay 1 p
    c = delay 0 (p .&. s)

adderSeq x y = res
  where c_in = delay 0 c_out
        res@(c_out, _) = fullAdder x y c_in
doom_adderSeq x y = res
  where c_in = delay 0 s
        res@(c_out, s) = fullAdder x y c_in
-- | prop
prop_addSeq x y = assert (adderSeq x y === adderSeq x y)
                         "Sequential adder equivalent to itself"
prop_brokenAddSeq x y = assert (adderSeq x y === doom_adderSeq x y)
                               "Broken seq adder is equivalent to working one"

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
  verifyLiveIncremental cnf (assert ((0 .&. dontCare) === inv (1 .|. dontCare :: Bit 1)) "don't care val 1 (Holds)")
  verifyLiveIncremental cnf (assert (0 === (dontCare :: Bit 1)) "don't care val 2 (Falsifiable)")
  verifyLiveIncremental cnf (assert (dontCare === (dontCare :: Bit 1)) "don't care val 3 (Falsifiable)")
  verifyLiveIncremental cnf (\(x :: Bit 1) -> assert (delay 0 x === delay dontCare x) "don't care reg 1 (Falsifiable)")
  verifyLiveIncremental cnf (\(x :: Bit 1) -> assert (delay dontCare x === delay dontCare x) "don't care reg 2 (Falsifiable)")
  verifyLiveIncremental cnf (\(x :: Bit 1) -> assert (delay 1 x === (delay 1 0 .|. delay dontCare x)) "don't care reg 3 (Holds)")
  verifyLiveIncremental cnf (\(x :: Bit 2) -> assert (delay ((0 :: Bit 1) # (dontCare :: Bit 1)) x === delay dontCare x) "don't care reg 4 (Falsifiable)")
  --verifyLiveFixed (verb, VerifConf { restrictedStates = True, write = write_nothing, giveModel = True }, FixedConf { depth = 4 }) (\x y -> assert (((test_seq x y) === (test_seq x y))) "test_seq === test_seq")
  --verifyLiveIncremental cnf (\x -> assert (((notId x) === (id x))) "notId === id")
  verifyLiveIncremental cnf (\x y -> assert (((adder2UnrollSeq x y) === (adder2UnrollSeq x y))) "aus === aus")
  --verifyLiveFixed (Verbose, vconfDefault, FixedConf { depth = 4 }) ausEqAus
  --verifyWith (dfltVerifyConf { verifyConfMode = Induction (fixedDepth 4) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }) ausEqAus
  --verifyWith cnfEasy prop_brokenAddSeq
  verifyLiveIncremental cnf prop_brokenAddSeq
  where
    cnfEasy = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }
    cnfHard = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = True, userConfIncreasePeriod = 4 } }
    cnfWrite = dfltVerifyConf { verifyConfMode = Induction (fixedDepth 3) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }

    verb = Info
    cnf = (verb, vconfDefault, iconfDefault)
