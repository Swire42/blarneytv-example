import Blarney
import Blarney.Nat
import qualified Blarney.SVec as V

type N = 2
type B1 = Bit 1
type Vec = V.SVec

incr :: Vec N B1 -> Vec N B1
incr xs = V.map fst (V.scanl (\(_, en) x -> (en .^. x, en .&. x)) (undefined, 1) xs)

decr :: Vec N B1 -> Vec N B1
decr xs = V.map fst (V.scanl (\(_, en) x -> (en .^. x, en .&. inv x)) (undefined, 1) xs)

outer :: B1 -> B1
outer guard = guard .|. (V.foldr (.&.) 1 $ V.zipWith (.^.) a (decr b))
  where
    a = delay zero $ incr a
    b = delay zero $ decr b

inner :: B1 -> B1
inner guard = V.foldr (.&.) 1 (V.map (guard .|.) (V.zipWith (.^.) a (decr b)))
  where
    a = delay zero $ incr a
    b = delay zero $ decr b

propOuter = \x -> assert (outer x) "outer"
propInner = \x -> assert (inner x) "inner"

main :: IO ()
main = do
  -- Safe-neighborhood k-induction, concurent, one-size-fits-all
  -- Outer/SN-Default
  verifyDefault (Info, vconfQuiet) propOuter
  -- Inner/SN-Default
  verifyDefault (Info, vconfQuiet) propInner

  -- Safe-neighborhood k-induction, fixed depth, single-threaded
  -- Outer/SN-Fixed
  verifyLiveQIFixed (Info, vconfDefault, FixedConf { depth=1 }) propOuter
  -- Inner/SN-Fixed
  verifyLiveQIFixed (Info, vconfDefault, FixedConf { depth=1 }) propInner
