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

halfAdder :: Bit 1 -> Bit 1 -> (Bit 1, Bit 1)
halfAdder a b = (a .&. b, a .^. b)

fullAdder :: (Bit 1, (Bit 1, Bit 1)) -> (Bit 1, Bit 1)
fullAdder (cIn, (a, b)) = (s1, cOut)
  where
    (c0, s0) = halfAdder a b
    (c1, s1) = halfAdder s0 cIn
    cOut = c0 .|. c1

combAdder :: (Bit 1, Bit 1) -> (Bit 1, Bit 1) -> (Bit 1, Bit 1)
combAdder (a0, a1) (b0, b1) = (out0, out1)
  where
    (out0, cOut0) = fullAdder (0, (a0, b0))
    (out1, cOut1) = fullAdder (cOut0, (a1, b1))

unrollAdder :: (Bit 1, Bit 1) -> (Bit 1, Bit 1) -> (Bit 1, Bit 1)
unrollAdder (a0, a1) (b0, b1) = (out0, out1)
  where
    (out0, cOut0) = fullAdder (cIn0, (a0, b0))
    (out1, cOut1) = fullAdder (cIn1, (a1, b1))
    cNext0       = reset0 ? (0, cOut0)
    cNext1       = reset1 ? (0, cOut1)
    cIn0         = delay 0 cNext1
    cIn1         = cNext0
    reset0 = delay 0 reset0
    reset1 = delay 1 reset1

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
  let smtDir = cwd ++ "/Check/"
  -- generate smt2 scripts
  --writeSMTScript cnfWrite (\x -> assert ((notId x) === x) "notId === id") "prop" smtDir
  --writeSMTScript cnfWrite (\x y -> assert (((delay 0 $ adderSeqUnrollBit @2 x y) === (delay 0 $ x + y))) "Inner") "inner" smtDir

  verifyWith cnfEasy (\x y -> assert (((combAdder x y) === (unrollAdder x y))) "combAdder === unrollAdder")
  verifyWith cnfEasy (\x y -> assert (((unrollAdder x y) === (unrollAdder x y))) "unrollAdder === unrollAdder")
  where
    cnfEasy = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }
    cnfHard = dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = True, userConfIncreasePeriod = 4 } }
    cnfWrite = dfltVerifyConf { verifyConfMode = Induction (fixedDepth 2) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }
