import System.Directory
import System.Environment

import Blarney
import qualified Blarney.SList as SList
import qualified Blarney.SVec as SVec
import qualified Blarney.TVec as TVec
import Blarney.Retime
import Blarney.ITranspose

import Control.Arrow ((***))

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
adderSeqUnroll :: forall n. KnownNat n => SVec.SVec n (Bit 1) -> SVec.SVec n (Bit 1) -> SVec.SVec n (Bit 1)
adderSeqUnroll a b = (unrollS @n $ adderSeqN (valueOf @n)) $ SVec.zip a b

adderSeqUnrollBit :: forall n. KnownNat n => Bit n -> Bit n -> Bit n
adderSeqUnrollBit a b = itranspose $ adderSeqUnroll @n (itranspose a) (itranspose b)

replace pos newVal list = take pos list ++ newVal : drop (pos+1) list

adderSeqUnrollSlowdown :: forall m. KnownNat m => Int -> SVec.SVec m (Bit 1, Bit 1) -> SVec.SVec m (Bit 1)
adderSeqUnrollSlowdown n = unrollS $ slowdown (valueOf @m) $ adderSeqN n

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

notId :: Bit 1 -> Bit 1
notId x = s
  where
    s = x .^. c
    p = delay 0 $ delay 1 p
    c = delay 0 (p .&. s)

adderSeqTVec :: forall n. (KnownNat n, 1 <= n) => TVec.TVec n (Bit 1) -> TVec.TVec n (Bit 1) -> TVec.TVec n (Bit 1)
adderSeqTVec a b = fst $ TVec.unzip $ TVec.scanReset (\(_, cIn) (a, b) -> fullAdder' (cIn, (a, b))) (TVec.replicate (0, 0)) $ TVec.zip a b

adderSeqTVecBitDelay :: forall n. (KnownNat n, 1 <= n) => Bit n -> Bit n -> Bit n
adderSeqTVecBitDelay a b = itranspose . TVec.collect (SVec.replicate 0) $ adderSeqTVec @n (TVec.sweep $ itranspose a) (TVec.sweep $ itranspose b)

main :: IO ()
main = do
  -- path to script output directory
  cwd <- getCurrentDirectory
  let smtDir = cwd ++ "/Check/"
  -- generate smt2 scripts
  --writeSMTScript cnfWrite (\x -> assert ((notId x) === x) "notId === id") "prop" smtDir
  --writeSMTScript cnfWrite (\x y -> assert (((delay 0 $ adderSeqUnrollBit @2 x y) === (delay 0 $ x + y))) "Inner") "inner" smtDir

  verifyWith cnfEasy (\x -> assert ((notId x) === x) "notId === id")
  verifyWith cnfEasy (\x y -> assert (adder @16 x y === x + y) "adder === +")
  verifyWith cnfEasy (\x y -> assert (adderSeqUnrollBit @16 x y === x + y) "adderSeqUnrollBit === +")
  verifyWith cnfEasy (\x y -> assert (adderSeqTVecBitDelay @2 x y === adderSeqTVecBitDelay @2 x y) "adderSeqUnrollBit === +")
  verifyWith cnfEasy (\x y -> assert ((test2 x y) === (x + y)) "test2: no delays")
  verifyWith cnfEasy (\x y -> assert (delay 1 ((test2 x y) === (x + y))) "test2: outer delay")
  verifyWith cnfEasy (\x y -> assert (((delay 0 (test2 x y)) === (delay 0 (x + y)))) "test2: inner delays")
  verifyWith cnfEasy (\x y -> assert ((adderSeqUnrollBit @2 x y) === (x + y)) "asu: no delays")
  verifyWith cnfEasy (\x y -> assert (delay 1 ((adderSeqUnrollBit @2 x y) === (x + y))) "asu: outer delay")
  verifyWith cnfHard (\x y -> assert ((delay 0 (adderSeqUnrollBit @2 x y)) === (delay 0 (x + y))) "asu: inner delays (too hard)")
  verifyWith cnfEasy (\x y -> assert ((adderSeqUnrollBit @2 x y) === (x + y)) "asu === +")
  verifyWith cnfEasy (\x y -> assert ((delay 0 $ x + y) === adderSeqTVecBitDelay @2 x y) "d.+ === astv")
  verifyWith cnfHard (\x y -> assert ((delay 0 $ adderSeqUnrollBit @2 x y) === adderSeqTVecBitDelay @2 x y) "d.asu === astv (too hard)")
  verifyWith cnfEasy (\x -> assert ((SVec.head $ f x) === 1) "unroll . slowdown === map // head")
  verifyWith cnfEasy (\x -> assert ((SVec.last $ f x) === 1) "unroll . slowdown === map // last")
  verifyWith cnfHard (\x -> assert ((SVec.head $ f x, SVec.last $ f x) === (1, 1)) "unroll . slowdown === map // head and last (too hard)")
  where
    cnfEasy = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }
    cnfHard = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = True, userConfIncreasePeriod = 4 } }
    cnfWrite = dfltVerifyConf { verifyConfMode = Induction (fixedDepth 2) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }
    f x = SVec.zipWith (===) (adderSeqUnrollSlowdown @2 2 x) (SVec.map (adderSeqN 2) x)
