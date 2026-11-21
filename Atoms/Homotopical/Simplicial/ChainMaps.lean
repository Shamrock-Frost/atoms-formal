import Atoms.ForMathlib.Data.Fin.SuccPred
import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision

open CategoryTheory

universe u

namespace Atoms.Homotopical

namespace MossUnit

open PartialOrder

abbrev Chains (n : ℕ) := NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))

def single (m v : ℕ) : Finset (ULift.{u} (Fin (m + 1))) :=
  Finset.univ.filter fun x ↦ x.down.val = v

def iic (m v : ℕ) : Finset (ULift.{u} (Fin (m + 1))) :=
  Finset.univ.filter fun x ↦ x.down.val ≤ v

@[simp]
theorem mem_single {m v : ℕ} {x : ULift.{u} (Fin (m + 1))} : x ∈ single m v ↔ x.down.val = v := by
  simp [single]

@[simp]
theorem mem_iic {m v : ℕ} {x : ULift.{u} (Fin (m + 1))} : x ∈ iic m v ↔ x.down.val ≤ v := by
  simp [iic]

def joinF {n m : ℕ} (G : ℕ → Finset (ULift.{u} (Fin (m + 1))))
    (S : Finset (ULift.{u} (Fin (n + 1)))) : Finset (ULift.{u} (Fin (m + 1))) :=
  S.biUnion fun a ↦ G a.down.val

theorem mem_joinF {n m : ℕ} {G : ℕ → Finset (ULift.{u} (Fin (m + 1)))}
    {S : Finset (ULift.{u} (Fin (n + 1)))} {x : ULift.{u} (Fin (m + 1))} :
    x ∈ joinF G S ↔ ∃ a ∈ S, x ∈ G a.down.val :=
  Finset.mem_biUnion

theorem joinF_joinF {n m l : ℕ} (G : ℕ → Finset (ULift.{u} (Fin (l + 1))))
    (H : ℕ → Finset (ULift.{u} (Fin (m + 1)))) (S : Finset (ULift.{u} (Fin (n + 1)))) :
    joinF G (joinF H S) = joinF (fun c ↦ joinF G (H c)) S := by
  ext x
  simp only [mem_joinF]
  constructor
  · rintro ⟨b, ⟨a, ha, hb⟩, hx⟩
    exact ⟨a, ha, b, hb, hx⟩
  · rintro ⟨a, ha, b, hb, hx⟩
    exact ⟨b, ⟨a, ha, hb⟩, hx⟩

theorem joinF_congr {n m : ℕ} {G H : ℕ → Finset (ULift.{u} (Fin (m + 1)))}
    (S : Finset (ULift.{u} (Fin (n + 1)))) (h : ∀ c ≤ n, G c = H c) :
    joinF G S = joinF H S :=
  Finset.biUnion_congr rfl fun a _ ↦ h _ (Nat.lt_succ_iff.1 a.down.isLt)

theorem joinF_single {n m : ℕ} (G : ℕ → Finset (ULift.{u} (Fin (m + 1)))) {v : ℕ}
    (hv : v ≤ n) : joinF G (single n v) = G v := by
  ext x
  simp only [mem_joinF, mem_single]
  constructor
  · rintro ⟨a, ha, hx⟩
    rwa [← ha]
  · intro hx
    exact ⟨⟨⟨v, by omega⟩⟩, rfl, hx⟩

theorem joinF_single_self {n : ℕ} (S : Finset (ULift.{u} (Fin (n + 1)))) :
    joinF (single n) S = S := by
  ext x
  simp only [mem_joinF, mem_single]
  constructor
  · rintro ⟨a, ha, hx⟩
    rwa [show x = a from ULift.ext _ _ (Fin.ext hx)]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem joinF_absorb {n m : ℕ} {G : ℕ → Finset (ULift.{u} (Fin (m + 1)))}
    {S : Finset (ULift.{u} (Fin (n + 1)))} {a : ULift.{u} (Fin (n + 1))} (ha : a ∈ S)
    (h : ∀ b ∈ S, G b.down.val ⊆ G a.down.val) : joinF G S = G a.down.val :=
  subset_antisymm (Finset.biUnion_subset.2 h)
    (Finset.subset_biUnion_of_mem (fun b ↦ G b.down.val) ha)

def joinHom (n m : ℕ) (G : ℕ → Finset (ULift.{u} (Fin (m + 1))))
    (hG : ∀ c ≤ n, (G c).Nonempty) : Chains n →o Chains m where
  toFun S :=
    { finset := joinF G S.finset
      nonempty := by
        obtain ⟨a, ha⟩ := S.nonempty
        obtain ⟨x, hx⟩ := hG _ (Nat.lt_succ_iff.1 a.down.isLt)
        exact ⟨x, mem_joinF.2 ⟨a, ha, hx⟩⟩
      comparable a b := le_total a.1 b.1 }
  monotone' _ _ h := Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem joinHom_finset {n m : ℕ} {G : ℕ → Finset (ULift.{u} (Fin (m + 1)))}
    {hG : ∀ c ≤ n, (G c).Nonempty} (S : Chains n) :
    (joinHom n m G hG S).finset = joinF G S.finset := rfl

theorem orderHom_ext {n m : ℕ} {φ ψ : Chains n →o Chains m}
    (h : ∀ S : Chains n, (φ S).finset = (ψ S).finset) : φ = ψ :=
  OrderHom.ext _ _ (funext fun S ↦ NonemptyFiniteChains.ext (h S))

def jGen (n k c : ℕ) : Finset (ULift.{u} (Fin (n + 1))) :=
  Finset.univ.filter fun x ↦ x.down.val = c ∨ (k < c ∧ x.down.val ≤ c)

def rGen (n k c : ℕ) : Finset (ULift.{u} (Fin (n + 1))) :=
  Finset.univ.filter fun x ↦ (c ≤ k ∧ x.down.val = c) ∨ (c = k + 1 ∧ x.down.val ≤ k) ∨
    (k + 1 < c ∧ x.down.val + 1 = c)

def dGen (n i c : ℕ) : Finset (ULift.{u} (Fin (n + 1))) :=
  Finset.univ.filter fun x ↦ (c < i ∧ x.down.val = c) ∨ (i ≤ c ∧ x.down.val = c + 1)

def sGen (n i c : ℕ) : Finset (ULift.{u} (Fin (n + 1))) :=
  Finset.univ.filter fun x ↦ (c ≤ i ∧ x.down.val = c) ∨ (i < c ∧ x.down.val + 1 = c)

@[simp]
theorem mem_jGen {n k c : ℕ} {x : ULift.{u} (Fin (n + 1))} :
    x ∈ jGen n k c ↔ x.down.val = c ∨ (k < c ∧ x.down.val ≤ c) := by
  simp [jGen]

@[simp]
theorem mem_rGen {n k c : ℕ} {x : ULift.{u} (Fin (n + 1))} :
    x ∈ rGen n k c ↔ (c ≤ k ∧ x.down.val = c) ∨ (c = k + 1 ∧ x.down.val ≤ k) ∨
      (k + 1 < c ∧ x.down.val + 1 = c) := by
  simp [rGen]

@[simp]
theorem mem_dGen {n i c : ℕ} {x : ULift.{u} (Fin (n + 1))} :
    x ∈ dGen n i c ↔ (c < i ∧ x.down.val = c) ∨ (i ≤ c ∧ x.down.val = c + 1) := by
  simp [dGen]

@[simp]
theorem mem_sGen {n i c : ℕ} {x : ULift.{u} (Fin (n + 1))} :
    x ∈ sGen n i c ↔ (c ≤ i ∧ x.down.val = c) ∨ (i < c ∧ x.down.val + 1 = c) := by
  simp [sGen]

local macro (name := tacticMemOmega) "mem_omega" : tactic =>
  `(tactic| (simp only [mem_single, mem_iic, mem_jGen, mem_rGen, mem_dGen, mem_sGen, and_true,
    true_and]; omega))

theorem jGen_of_le {n k c : ℕ} (h : c ≤ k) : jGen n k c = single n c := by
  ext x; rw [mem_jGen, mem_single]; omega

theorem jGen_of_lt {n k c : ℕ} (h : k < c) : jGen n k c = iic n c := by
  ext x; rw [mem_jGen, mem_iic]; omega

theorem rGen_of_le {n k c : ℕ} (h : c ≤ k) : rGen n k c = single n c := by
  ext x; rw [mem_rGen, mem_single]; omega

theorem rGen_of_eq {n k c : ℕ} (h : c = k + 1) : rGen n k c = iic n k := by
  ext x; rw [mem_rGen, mem_iic]; omega

theorem rGen_of_lt {n k c : ℕ} (h : k + 1 < c) : rGen n k c = single n (c - 1) := by
  ext x; rw [mem_rGen, mem_single]; omega

theorem dGen_of_lt {n i c : ℕ} (h : c < i) : dGen n i c = single n c := by
  ext x; rw [mem_dGen, mem_single]; omega

theorem dGen_of_le {n i c : ℕ} (h : i ≤ c) : dGen n i c = single n (c + 1) := by
  ext x; rw [mem_dGen, mem_single]; omega

theorem sGen_of_le {n i c : ℕ} (h : c ≤ i) : sGen n i c = single n c := by
  ext x; rw [mem_sGen, mem_single]; omega

theorem sGen_of_lt {n i c : ℕ} (h : i < c) : sGen n i c = single n (c - 1) := by
  ext x; rw [mem_sGen, mem_single]; omega

theorem joinF_jGen_iic {n k v : ℕ} : joinF (jGen n k) (iic n v) = iic n v := by
  ext x
  simp only [mem_joinF, mem_iic, mem_jGen]
  constructor
  · rintro ⟨a, ha, h⟩
    omega
  · intro hx
    exact ⟨x, hx, Or.inl rfl⟩

theorem joinF_rGen_iic_of_le {n k v : ℕ} (hv : v ≤ k) :
    joinF (rGen n k) (iic (n + 1) v) = iic n v := by
  ext x
  simp only [mem_joinF, mem_iic, mem_rGen]
  constructor
  · rintro ⟨a, ha, h⟩
    omega
  · intro hx
    exact ⟨⟨⟨x.down.val, by omega⟩⟩, by mem_omega, by mem_omega⟩

theorem joinF_rGen_iic_of_lt {n k v : ℕ} (hv : k < v) :
    joinF (rGen n k) (iic (n + 1) v) = iic n (v - 1) := by
  ext x
  simp only [mem_joinF, mem_iic, mem_rGen]
  constructor
  · rintro ⟨a, ha, h⟩
    omega
  · intro hx
    by_cases hxk : x.down.val ≤ k
    · exact ⟨⟨⟨x.down.val, by omega⟩⟩, by mem_omega, by mem_omega⟩
    · exact ⟨⟨⟨x.down.val + 1, by omega⟩⟩, by mem_omega, by mem_omega⟩

theorem joinF_sGen_iic_of_le {n i v : ℕ} (hv : v ≤ i) :
    joinF (sGen n i) (iic (n + 1) v) = iic n v := by
  ext x
  simp only [mem_joinF, mem_iic, mem_sGen]
  constructor
  · rintro ⟨a, ha, h⟩
    omega
  · intro hx
    exact ⟨⟨⟨x.down.val, by omega⟩⟩, by mem_omega, by mem_omega⟩

theorem joinF_sGen_iic_of_lt {n i v : ℕ} (hv : i < v) :
    joinF (sGen n i) (iic (n + 1) v) = iic n (v - 1) := by
  ext x
  simp only [mem_joinF, mem_iic, mem_sGen]
  constructor
  · rintro ⟨a, ha, h⟩
    omega
  · intro hx
    by_cases hxi : x.down.val ≤ i
    · exact ⟨⟨⟨x.down.val, by omega⟩⟩, by mem_omega, by mem_omega⟩
    · exact ⟨⟨⟨x.down.val + 1, by omega⟩⟩, by mem_omega, by mem_omega⟩

theorem joinF_dGen_iic {n i v : ℕ} (hv : v < i) (hvn : v ≤ n) :
    joinF (dGen (n + 1) i) (iic n v) = iic (n + 1) v := by
  ext x
  simp only [mem_joinF, mem_iic, mem_dGen]
  constructor
  · rintro ⟨a, ha, h⟩
    omega
  · intro hx
    exact ⟨⟨⟨x.down.val, by omega⟩⟩, by mem_omega, by mem_omega⟩

def jMap (n k : ℕ) : Chains n →o Chains n :=
  joinHom n n (jGen n k) fun c hc ↦ ⟨⟨⟨c, by omega⟩⟩, by simp⟩

def rMap (n k : ℕ) (hk : k ≤ n) : Chains (n + 1) →o Chains n :=
  joinHom (n + 1) n (rGen n k) fun c hc ↦ by
    by_cases h : c ≤ k
    · exact ⟨⟨⟨c, by omega⟩⟩, by mem_omega⟩
    · exact ⟨⟨⟨c - 1, by omega⟩⟩, by mem_omega⟩

def sdCoface (n i : ℕ) : Chains n →o Chains (n + 1) :=
  joinHom n (n + 1) (dGen (n + 1) i) fun c hc ↦ by
    by_cases h : c < i
    · exact ⟨⟨⟨c, by omega⟩⟩, by mem_omega⟩
    · exact ⟨⟨⟨c + 1, by omega⟩⟩, by mem_omega⟩

def sdCodegeneracy (n i : ℕ) (hi : i ≤ n) : Chains (n + 1) →o Chains n :=
  joinHom (n + 1) n (sGen n i) fun c hc ↦ by
    by_cases h : c ≤ i
    · exact ⟨⟨⟨c, by omega⟩⟩, by mem_omega⟩
    · exact ⟨⟨⟨c - 1, by omega⟩⟩, by mem_omega⟩

theorem orderHomMap_δ (n : ℕ) (i : Fin (n + 2)) :
    NonemptyFiniteChains.orderHomMap (SimplexCategory.toPartOrd.{u}.map (SimplexCategory.δ i)).hom =
      sdCoface n i.val := by
  apply orderHom_ext
  intro S
  ext x
  refine (@Finset.mem_image _ _ (fun a b ↦ Classical.propDecidable (a = b)) _ _ _).trans ?_
  simp only [sdCoface, joinHom_finset, mem_joinF, mem_dGen]
  refine exists_congr fun (a : ULift.{u} (Fin (n + 1))) ↦ and_congr_right fun _ ↦ ?_
  change (ULift.up (i.succAbove a.down) : ULift.{u} (Fin (n + 2))) = x ↔ _
  rw [ULift.ext_iff, Fin.ext_iff, Fin.val_succAbove]
  split_ifs <;> omega

theorem orderHomMap_σ (n : ℕ) (i : Fin (n + 1)) :
    NonemptyFiniteChains.orderHomMap (SimplexCategory.toPartOrd.{u}.map (SimplexCategory.σ i)).hom =
      sdCodegeneracy n i.val (Nat.lt_succ_iff.1 i.isLt) := by
  apply orderHom_ext
  intro S
  ext x
  refine (@Finset.mem_image _ _ (fun a b ↦ Classical.propDecidable (a = b)) _ _ _).trans ?_
  simp only [sdCodegeneracy, joinHom_finset, mem_joinF, mem_sGen]
  refine exists_congr fun (a : ULift.{u} (Fin (n + 2))) ↦ and_congr_right fun _ ↦ ?_
  change (ULift.up (i.predAbove a.down) : ULift.{u} (Fin (n + 1))) = x ↔ _
  rw [ULift.ext_iff, Fin.ext_iff, Fin.val_predAbove]
  split_ifs <;> omega

def JoinPres {n m : ℕ}
    (Φ : Finset (ULift.{u} (Fin (n + 1))) → Finset (ULift.{u} (Fin (m + 1)))) : Prop :=
  ∀ T, Φ T = joinF (fun c ↦ Φ (single n c)) T

theorem joinPres_joinF {n m : ℕ} (G : ℕ → Finset (ULift.{u} (Fin (m + 1)))) :
    JoinPres (n := n) fun T ↦ joinF G T :=
  fun T ↦ joinF_congr T fun _ hc ↦ (joinF_single G hc).symm

theorem JoinPres.comp {n m l : ℕ} (G : ℕ → Finset (ULift.{u} (Fin (l + 1))))
    {Φ : Finset (ULift.{u} (Fin (n + 1))) → Finset (ULift.{u} (Fin (m + 1)))}
    (hΦ : JoinPres Φ) : JoinPres fun T ↦ joinF G (Φ T) :=
  fun T ↦ (congrArg (joinF G) (hΦ T)).trans (joinF_joinF _ _ _)

theorem JoinPres.ext {n m : ℕ}
    {Φ Ψ : Finset (ULift.{u} (Fin (n + 1))) → Finset (ULift.{u} (Fin (m + 1)))}
    (hΦ : JoinPres Φ) (hΨ : JoinPres Ψ) (h : ∀ c ≤ n, Φ (single n c) = Ψ (single n c))
    (T : Finset (ULift.{u} (Fin (n + 1)))) : Φ T = Ψ T := by
  rw [hΦ, hΨ]
  exact joinF_congr T h

theorem JoinPres.eq_of_absorb {n m : ℕ}
    {Φ : Finset (ULift.{u} (Fin (n + 1))) → Finset (ULift.{u} (Fin (m + 1)))}
    (hΦ : JoinPres Φ) {v : ℕ} (hv : v ≤ n)
    (h : ∀ b ≤ v, Φ (single n b) ⊆ Φ (single n v)) : Φ (iic n v) = Φ (single n v) := by
  rw [hΦ]
  exact joinF_absorb (a := ⟨⟨v, by omega⟩⟩) (by simp) fun b hb ↦ h _ (by simpa using hb)

local macro (name := tacticMossEval) "moss_eval" : tactic =>
  `(tactic| simp (disch := omega) only [jGen_of_le, jGen_of_lt, rGen_of_le, rGen_of_eq,
    rGen_of_lt, dGen_of_lt, dGen_of_le, sGen_of_le, sGen_of_lt, joinF_single, joinF_jGen_iic,
    joinF_rGen_iic_of_le, joinF_rGen_iic_of_lt, joinF_sGen_iic_of_le, joinF_sGen_iic_of_lt,
    joinF_dGen_iic])

local macro (name := tacticMossClose) "moss_close" : tactic =>
  `(tactic| first | rfl | (exfalso; omega) | (congr 1; omega) | (ext x; mem_omega))

local macro (name := tacticMossSolve) "moss_solve" : tactic =>
  `(tactic| (moss_eval <;> moss_close))

local macro (name := tacticJoinPres) "join_pres" : tactic =>
  `(tactic| repeat' first | exact joinPres_joinF _ | apply JoinPres.comp)

theorem jMap_comp_jMap (n k l : ℕ) (h : k ≤ l) : (jMap n k).comp (jMap n l) = jMap n k := by
  apply orderHom_ext
  intro S
  change joinF (jGen n k) (joinF (jGen n l) S.finset) = joinF (jGen n k) S.finset
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c l <;> moss_solve

theorem rMap_comp_sdCoface (n k : ℕ) (hk : k ≤ n) : (rMap n k hk).comp (sdCoface n (k + 1)) =
    OrderHom.id := by
  apply orderHom_ext
  intro S
  change joinF (rGen n k) (joinF (dGen (n + 1) (k + 1)) S.finset) = S.finset
  conv_rhs => rw [← joinF_single_self S.finset]
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c k <;> moss_solve

theorem jMap_comp_rMap_comp_sdCoface_comp_jMap (n k i : ℕ) (hk : k ≤ n) (hk1 : 1 ≤ k) (hi : i ≤ k) :
    (jMap n k).comp ((rMap n k hk).comp ((sdCoface n i).comp (jMap n (k - 1)))) =
      (jMap n k).comp ((rMap n k hk).comp (sdCoface n i)) := by
  apply orderHom_ext
  intro S
  change joinF (jGen n k) (joinF (rGen n k) (joinF (dGen (n + 1) i)
    (joinF (jGen n (k - 1)) S.finset))) =
      joinF (jGen n k) (joinF (rGen n k) (joinF (dGen (n + 1) i) S.finset))
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c (k - 1)
  · moss_eval
  · rw [joinF_single _ hc, jGen_of_lt (by omega)]
    refine (JoinPres.eq_of_absorb (Φ := fun T ↦ joinF (jGen n k) (joinF (rGen n k)
      (joinF (dGen (n + 1) i) T))) (by join_pres) hc fun b hb ↦ ?_)
    intro x hx
    have hc' : joinF (jGen n k) (joinF (rGen n k) (joinF (dGen (n + 1) i) (single n c))) =
        iic n c := by
      obtain h2 | h2 := eq_or_lt_of_le (show k ≤ c by omega)
      · subst h2
        moss_eval
      · moss_eval
        moss_close
    rw [hc', mem_iic]
    simp only [mem_joinF, mem_single, mem_jGen, mem_rGen, mem_dGen] at hx
    obtain ⟨a, ⟨a', ⟨a'', h1, h2⟩, h3⟩, h4⟩ := hx
    omega

theorem rMap_comp_sdCoface_of_lt (m k i : ℕ) (hk : k ≤ m) (hi : k + 2 ≤ i) :
    (rMap (m + 1) k (by omega)).comp (sdCoface (m + 1) i) =
      (sdCoface m (i - 1)).comp (rMap m k hk) := by
  apply orderHom_ext
  intro S
  change joinF (rGen (m + 1) k) (joinF (dGen (m + 2) i) S.finset) =
    joinF (dGen (m + 1) (i - 1)) (joinF (rGen m k) S.finset)
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c k <;> obtain h2 | h2 := le_or_gt c (k + 1) <;>
    obtain h3 | h3 := lt_or_ge c i <;> moss_solve

theorem rMap_comp_jMap (n k h : ℕ) (hk : k ≤ n) (hh : h ≤ k) :
    (rMap n k hk).comp (jMap (n + 1) h) = (jMap n h).comp (rMap n k hk) := by
  apply orderHom_ext
  intro S
  change joinF (rGen n k) (joinF (jGen (n + 1) h) S.finset) =
    joinF (jGen n h) (joinF (rGen n k) S.finset)
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c h <;> obtain h2 | h2 := le_or_gt c k <;>
    obtain h3 | h3 := le_or_gt c (k + 1) <;> moss_solve

theorem jMap_comp_sdCoface_comp_jMap (n k i : ℕ) :
    (jMap (n + 1) k).comp ((sdCoface n i).comp (jMap n k)) =
      (jMap (n + 1) k).comp (sdCoface n i) := by
  apply orderHom_ext
  intro S
  change joinF (jGen (n + 1) k) (joinF (dGen (n + 1) i) (joinF (jGen n k) S.finset)) =
    joinF (jGen (n + 1) k) (joinF (dGen (n + 1) i) S.finset)
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c k
  · moss_eval
  · rw [joinF_single _ hc, jGen_of_lt h1]
    refine (JoinPres.eq_of_absorb (Φ := fun T ↦ joinF (jGen (n + 1) k)
      (joinF (dGen (n + 1) i) T)) (by join_pres) hc fun b hb ↦ ?_)
    intro x hx
    simp only [mem_joinF, mem_single, mem_jGen, mem_dGen] at hx ⊢
    obtain ⟨a, ⟨a', h2, h3⟩, h4⟩ := hx
    refine ⟨⟨⟨if c < i then c else c + 1, by split_ifs <;> omega⟩⟩,
      ⟨⟨⟨c, by omega⟩⟩, rfl, by split_ifs <;> mem_omega⟩, ?_⟩
    split_ifs <;> mem_omega

theorem jMap_comp_rMap (m k h : ℕ) (hk : k ≤ m) (hh : h < k) :
    (jMap m h).comp (rMap m k hk) = (jMap m h).comp (sdCodegeneracy m k hk) := by
  apply orderHom_ext
  intro S
  change joinF (jGen m h) (joinF (rGen m k) S.finset) =
    joinF (jGen m h) (joinF (sGen m k) S.finset)
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c k <;> obtain h2 | h2 := le_or_gt c (k + 1) <;>
    moss_solve

theorem jMap_comp_rMap_comp_rMap (m k : ℕ) (hk : k ≤ m) :
    (jMap m k).comp ((rMap m k hk).comp (rMap (m + 1) k (by omega))) =
      (jMap m k).comp ((rMap m k hk).comp (sdCodegeneracy (m + 1) (k + 1) (by omega))) := by
  apply orderHom_ext
  intro S
  change joinF (jGen m k) (joinF (rGen m k) (joinF (rGen (m + 1) k) S.finset)) =
    joinF (jGen m k) (joinF (rGen m k) (joinF (sGen (m + 1) (k + 1)) S.finset))
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c k <;> obtain h2 | h2 := le_or_gt c (k + 1) <;>
    obtain h3 | h3 := le_or_gt c (k + 2) <;> moss_solve

theorem sdCodegeneracy_comp_jMap_comp_rMap_succ (n k h : ℕ) (hk : k ≤ n) (hh : h ≤ k) :
    (sdCodegeneracy n h (by omega)).comp
        ((jMap (n + 1) (k + 1)).comp (rMap (n + 1) (k + 1) (by omega))) =
      (jMap n k).comp ((rMap n k hk).comp (sdCodegeneracy (n + 1) h (by omega))) := by
  apply orderHom_ext
  intro S
  change joinF (sGen n h) (joinF (jGen (n + 1) (k + 1)) (joinF (rGen (n + 1) (k + 1))
    S.finset)) = joinF (jGen n k) (joinF (rGen n k) (joinF (sGen (n + 1) h) S.finset))
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c h <;> obtain h2 | h2 := le_or_gt c (k + 1) <;>
    obtain h3 | h3 := le_or_gt c (k + 2) <;> moss_solve

theorem sdCodegeneracy_comp_jMap_comp_rMap (n k h : ℕ) (hk : k ≤ n) (hh : k ≤ h) (hn : h ≤ n) :
    (sdCodegeneracy n h hn).comp ((jMap (n + 1) k).comp (rMap (n + 1) k (by omega))) =
      (jMap n k).comp ((rMap n k hk).comp (sdCodegeneracy (n + 1) (h + 1) (by omega))) := by
  apply orderHom_ext
  intro S
  change joinF (sGen n h) (joinF (jGen (n + 1) k) (joinF (rGen (n + 1) k) S.finset)) =
    joinF (jGen n k) (joinF (rGen n k) (joinF (sGen (n + 1) (h + 1)) S.finset))
  generalize S.finset = T
  revert T
  refine JoinPres.ext (by join_pres) (by join_pres) fun c hc ↦ ?_
  obtain h1 | h1 := le_or_gt c k <;> obtain h2 | h2 := le_or_gt c (k + 1) <;>
    obtain h3 | h3 := le_or_gt c (h + 1) <;> obtain h4 | h4 := le_or_gt c (k + 2) <;>
    moss_solve

end MossUnit

end Atoms.Homotopical
