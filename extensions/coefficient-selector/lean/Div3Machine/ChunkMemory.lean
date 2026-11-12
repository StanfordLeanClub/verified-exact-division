import Div3Machine.Stores

namespace Div3Machine
open Div3IEEE

theorem prefix_advance_initial (initial current : Memory) (src dst n i : ℕ) (ws : List Word)
    (ha : DisjointOrEqual src dst n) (hi : i+ws.length ≤ n)
    (inv : Prefix initial current src dst n i)
    (values : ∀ k (hk : k < ws.length), decode ws[k] =
      reference (decode (read32 initial (src+4*(i+k))))) :
    Prefix initial (writeWords current (dst+4*i) ws) src dst n (i+ws.length) := by
  apply prefix_advance initial current src dst n i ws ha hi inv
  intro k hk
  rw [inv.unread (i+k) (by omega) (by omega)]
  exact values k hk

theorem prefix_vector (initial current : Memory) (src dst n i : ℕ) (v : Vec)
    (ha : DisjointOrEqual src dst n) (hi : i+8 ≤ n)
    (inv : Prefix initial current src dst n i)
    (values : ∀ j : Fin 8, decode (v j) =
      reference (decode (read32 initial (src+4*(i+j.val))))) :
    Prefix initial (writeVec current (dst+4*i) v) src dst n (i+8) := by
  have h := prefix_advance_initial initial current src dst n i (List.ofFn v) ha
    (by simpa using hi) inv (by
      intro k hk
      have hk8 : k < 8 := by simpa using hk
      simpa only [List.getElem_ofFn] using values ⟨k,hk8⟩)
  simpa only [writeVec,List.length_ofFn] using h

theorem prefix_four (initial current : Memory) (src dst n i : ℕ) (v0 v1 v2 v3 : Vec)
    (ha : DisjointOrEqual src dst n) (hi : i+32 ≤ n)
    (inv : Prefix initial current src dst n i)
    (h0 : ∀ j : Fin 8, decode (v0 j) = reference (decode (read32 initial (src+4*(i+j.val)))))
    (h1 : ∀ j : Fin 8, decode (v1 j) = reference (decode (read32 initial (src+4*(i+8+j.val)))))
    (h2 : ∀ j : Fin 8, decode (v2 j) = reference (decode (read32 initial (src+4*(i+16+j.val)))))
    (h3 : ∀ j : Fin 8, decode (v3 j) = reference (decode (read32 initial (src+4*(i+24+j.val))))) :
    Prefix initial (fourStores current (dst+4*i) v0 v1 v2 v3) src dst n (i+32) := by
  have p0 := prefix_vector initial current src dst n i v0 ha (by omega) inv h0
  have p1 := prefix_vector initial _ src dst n (i+8) v1 ha (by omega) p0 h1
  have h16 : i+8+8=i+16 := by omega
  rw [h16] at p1
  have p2 := prefix_vector initial _ src dst n (i+16) v2 ha (by omega) p1 h2
  have h24 : i+16+8=i+24 := by omega
  rw [h24] at p2
  have p3 := prefix_vector initial _ src dst n (i+24) v3 ha (by omega) p2 h3
  convert p3 using 1 <;> simp only [fourStores] <;> congr 1 <;> omega

end Div3Machine
