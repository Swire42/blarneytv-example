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
  verifyDefault (Info, vconfQuiet) propOuter
  verifyDefault (Info, vconfQuiet) propInner

  -- Safe-neighborhood k-induction, fixed depth, single-threaded
  verifyLiveQIFixed (Info, vconfDefault, FixedConf { depth=1 }) propOuter
  verifyLiveQIFixed (Info, vconfDefault, FixedConf { depth=1 }) propInner

  -- Loop-free k-induction, single-threaded, incremental
  --verifyLiveIncremental (Info, vconfDefault, iconfDefault) propOuter
  --verifyLiveIncremental (Info, vconfDefault, iconfDefault) propInner

  -- Old verification backend, single-threaded, incremental
  --verifyWith (dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }) propOuter
  --verifyWith (dfltVerifyConf { verifyConfMode = Induction (IncreaseFrom 1) True, verifyConfUser = dfltUserConf { userConfInteractive = False } }) propInner

  return ()
