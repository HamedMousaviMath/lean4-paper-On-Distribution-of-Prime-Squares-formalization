import PrimeSquares.TimePrefixFinitePairing
open Finset
namespace PrimeSquares
theorem natural_prefix_filter (L K : ℕ) : (range L).filter (fun q => q ≤ K)=range (min L (K+1)) := by
  ext q
  simp only [mem_filter,mem_range,lt_min_iff]
  omega
end PrimeSquares
