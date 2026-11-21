import Atoms.Molecule.Cylinder.Inverted
import Atoms.Molecule.Layering.Existence
import Atoms.Molecule.Pasting.AtSubmolecule

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

namespace InvertedCylinder

open PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U} {ε : Bool} {x y : U}

theorem isMoleculeIn_front {V : LowerSet U} {e : ℕ}
    (hVU : U.IsSubmoleculeOf V ⊤)
    (hdV : krullDim V = ((e + 1 : ℕ) : WithBot ℕ∞)) (hKU : K ≤ U.boundary ⊤ e ε) :
    IsMoleculeIn (invertedCylinder U K ε (e + 1))
        (copy K (!ε) V ⊔ over K (U.boundary V e ε) ⊔ copy K ε V) ∧
      (invertedCylinder U K ε (e + 1)).IsSubmoleculeOf (over K (U.boundary V e ε))
        (copy K (!ε) V ⊔ over K (U.boundary V e ε) ⊔ copy K ε V) ∧
      (invertedCylinder U K ε (e + 1)).boundary
          (copy K (!ε) V ⊔ over K (U.boundary V e ε) ⊔ copy K ε V) e (!ε) =
        (partialCylinder U K).boundary (over K V) e (!ε) ∧
      (invertedCylinder U K ε (e + 1)).boundary
          (copy K (!ε) V ⊔ over K (U.boundary V e ε) ⊔ copy K ε V) e ε =
        (invertedCylinder U K ε (e + 1)).boundary
          (copy K ε V ⊔ (partialCylinder U K).boundary (over K V) e ε) e ε ∧
      (U.IsRound V → (invertedCylinder U K ε (e + 1)).IsRound
          (copy K (!ε) V ⊔ over K (U.boundary V e ε) ⊔ copy K ε V)) := by
  classical
  have hV : IsMoleculeIn U V := hVU.isMoleculeIn
  have gV := hV.isGlobular
  have hKd := dim_lt_of_mem_K hKU
  have KV : K ⊓ V ≤ U.boundary V e ε := fun z hz =>
    hVU.inf_boundary_le e ε ⟨hz.2, hKU hz.1⟩
  have S := cylinderStatement_of_isMoleculeIn (K := K) _ V rfl hV
  have IH : CylinderBelow K V := fun W _ hmW => cylinderStatement_of_isMoleculeIn _ W rfl hmW
  set A := copy K (!ε) V ⊔ over K (U.boundary V e ε) with hAdef
  set B := copy K ε V with hBdef
  have hVself : U.boundary V (e + 1) (!ε) = V := boundary_eq_self hdV.le _
  have hAeq : (partialCylinder U K).boundary (over K V) (e + 1) (!ε) = A := by
    rw [boundary_over_succ gV, hVself, Bool.not_not]
  have hA_P : IsMoleculeIn (partialCylinder U K) A :=
    hAeq ▸ S.1.boundary (e + 1) (!ε)
  have hAstd : A ≤ std K ε (e + 1) := by
    refine sup_le (fun z hz => ?_) fun z hz => mem_std_of_dim_lt ?_
    · rw [← (mem_copy.1 hz).2]; exact endpoint_notMem_std _
    · have := grade_le_of_mem_boundary (mem_over.1 hz)
      omega
  have hA : IsMoleculeIn (invertedCylinder U K ε (e + 1)) A :=
    (isMoleculeIn_iff_of_subset_std hAstd).2 hA_P
  have hB : IsMoleculeIn (invertedCylinder U K ε (e + 1)) B := by
    rw [hBdef, ← map_endpointDual hKd]
    exact (isMoleculeIn_map_iff (endpointDual U K ε hKd) V).2 ((isMoleculeIn_dual _).2 hV)
  have hdB : krullDim B = ((e + 1 : ℕ) : WithBot ℕ∞) := (krullDim_copy ε V).trans hdV
  have hdA : krullDim A = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    le_antisymm (hAeq ▸ krullDim_boundary_le (P := partialCylinder U K) _ (e + 1) (!ε))
      (by rw [← hdV, ← krullDim_copy (K := K) (!ε) V]; exact LowerSet.krullDim_mono le_sup_left)
  have hbB : (invertedCylinder U K ε (e + 1)).boundary B e (!ε) = copy K ε (U.boundary V e ε) := by
    rw [hBdef, boundary_copy_eps hKd, Bool.not_not]
  have hint : A ⊓ B = (invertedCylinder U K ε (e + 1)).boundary B e (!ε) := by
    rw [hbB, hAdef, hBdef, inf_sup_right, inf_comm (copy K (!ε) V), copy_inf_copy_not,
      inf_idem, inf_comm V K, inf_comm (over K _), copy_inf_over,
      inf_eq_right.2 (boundary_le V e ε), ← copy_sup, sup_eq_right.2 KV]
  have hPe : (partialCylinder U K).boundary (over K V) e ε ≤ std K ε (e + 1) :=
    subset_std_of_dimOf_lt (lt_of_le_of_lt (krullDim_boundary_le _ e ε)
      (by exact_mod_cast Nat.lt_succ_self e))
  have hsub : (invertedCylinder U K ε (e + 1)).IsSubmoleculeOf
      ((invertedCylinder U K ε (e + 1)).boundary B e (!ε))
      ((invertedCylinder U K ε (e + 1)).boundary A e ε) := by
    rw [hbB, boundary_eq_of_subset_std hAstd, ← hAeq,
      (isGlobular_over gV) e (e + 1) (Nat.lt_succ_self e)]
    exact isSubmoleculeOf_of_subset_std hPe
      (isSubmoleculeOf_copy_boundary_of_lt hV IH
        (by rw [hdV]; exact_mod_cast Nat.lt_succ_self e) ε)
  obtain ⟨m1, s1, -, b1, b2, r⟩ :=
    isMoleculeIn_sup_of_isSubmoleculeOf_boundary_boundary hA hB hsub hint
  have hover : (invertedCylinder U K ε (e + 1)).IsSubmoleculeOf (over K (U.boundary V e ε)) A := by
    have t := (S.2 (e + 1) hdV (!ε)).2 (Nat.succ_pos e)
    rw [Nat.add_sub_cancel, Bool.not_not, hAeq] at t
    exact isSubmoleculeOf_of_subset_std hAstd t
  refine ⟨m1, hover.trans s1, ?_, ?_, fun hr => ?_⟩
  · rw [b1, boundary_eq_of_subset_std hAstd, ← hAeq,
      (isGlobular_over gV) e (e + 1) (Nat.lt_succ_self e)]
  · rw [b2, boundary_eq_of_subset_std hAstd, ← hAeq,
      (isGlobular_over gV) e (e + 1) (Nat.lt_succ_self e)]
  · have hKV' : K ⊓ V ≤ U.bdryFull V :=
      KV.trans (bdry_eq_boundary hdV ε ▸ bdry_le_bdryFull V ε)
    have hrA : (partialCylinder U K).IsRound A :=
      hAeq ▸ (isRound_over hr hKV').boundary (e + 1) (!ε)
    refine r ((round_iff_of_subset_std hAstd).2 hrA) hdA ?_
    rw [LowerSet.krullDim_sup, hdA, hdB, max_self]; rfl

theorem boundary_front_eps {V : LowerSet U} {e : ℕ} (gX : U.IsGlobular V)
    (hKd : ∀ z ∈ K, grade ℕ z < e + 1) :
    (invertedCylinder U K ε (e + 1)).boundary
        (copy K ε V ⊔ (partialCylinder U K).boundary (over K V) e ε) e ε =
      (partialCylinder U K).boundary (over K (U.boundary V e (!ε))) e ε := by
  classical
  set W := U.boundary V e (!ε) with hWdef
  have gW : U.IsGlobular W := gX.boundary e (!ε)
  have hWself : U.boundary W e ε = W := boundary_eq_self (krullDim_boundary_le V e (!ε)) ε
  have hB : (invertedCylinder U K ε (e + 1)).boundary (copy K ε V) e ε = copy K ε W :=
    boundary_copy_eps hKd V ε
  set D := (partialCylinder U K).boundary (over K V) e ε with hDdef
  have hdD : krullDim D ≤ e := krullDim_boundary_le (P := partialCylinder U K) (over K V) e ε
  rw [sup_comm,
    boundary_sup_eq_lowerClosure_sdiff_sup (P := invertedCylinder U K ε (e + 1)) hdD, hB]
  rcases Nat.eq_zero_or_pos e with rfl | hpos
  · have hDB : (D : Set (partialCylinder U K)) ⊆ copy K ε V := by
      rw [hDdef, boundary_over_zero]; exact copy_mono ε (boundary_le V 0 ε)
    rw [sdiff_eq_empty.2 hDB, lowerClosure_empty, bot_sup_eq,
      boundary_over_zero, hWself]
  · obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    have hD : D = copy K ε (U.boundary V (f + 1) ε) ⊔ over K (U.boundary V f (!ε)) :=
      boundary_over_succ gX f ε
    rw [boundary_over_succ gW, hWself, gX f (f + 1) (Nat.lt_succ_self f)]
    refine le_antisymm (sup_le (lowerClosure_le.2 ?_) le_sup_left)
      (sup_le le_sup_right fun z hz => ?_)
    · rintro d ⟨hdD, hdB⟩
      rw [hD] at hdD
      rcases hdD with h | h
      · exact (hdB (copy_mono ε (boundary_le V _ ε) h)).elim
      · exact Or.inr h
    · by_cases hzB : z ∈ copy K ε V
      · exact Or.inr (mem_copy.2 ⟨gX.boundary_le_boundary (Nat.lt_succ_self f) _ _ (mem_over.1 hz),
          (mem_copy.1 hzB).2⟩)
      · exact Or.inl (subset_lowerClosure ⟨hD ▸ Or.inr hz, hzB⟩)

theorem krullDim_over_top {V : LowerSet U} {e : ℕ}
    (hKd : ∀ z ∈ K, grade ℕ z < e + 1) (hdV : krullDim V = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    krullDim (over K V) = ((e + 2 : ℕ) : WithBot ℕ∞) := by
  refine le_antisymm (krullDim_over_le hdV.le) ?_
  obtain ⟨⟨y, hyV⟩, hdy⟩ := coe_lt_krullDim_iff.1
    (show (e : WithBot ℕ∞) < krullDim V by rw [hdV]; exact_mod_cast Nat.lt_succ_self e)
  have hy' : e + 1 ≤ grade ℕ y := by exact_mod_cast hdy
  have hyle : grade ℕ y ≤ e + 1 := krullDim_le_coe_iff.1 hdV.le ⟨y, hyV⟩
  have hyK : y ∉ K := fun h => (hKd y h).not_ge hy'
  have := grade_add_one_le_krullDim_over (K := K) hyV hyK
  rwa [show grade ℕ y = e + 1 by omega] at this

theorem front_inf_le {X : LowerSet U} {e : ℕ} (gX : U.IsGlobular X)
    (hdW : krullDim (U.boundary X e (!ε)) = e)
    (hbW : U.boundary X e ε ⊓ U.boundary X e (!ε) ≤ U.bdryFull (U.boundary X e (!ε))) :
    (copy K (!ε) X ⊔ over K (U.boundary X e ε) ⊔ copy K ε X) ⊓
        over K (U.boundary X e (!ε)) ≤
      (partialCylinder U K).boundaryFull (over K (U.boundary X e (!ε))) e := by
  set W := U.boundary X e (!ε) with hWdef
  have gW : U.IsGlobular W := gX.boundary e (!ε)
  have hcopy (β : Bool) : copy K β X ⊓ over K W ≤
      (partialCylinder U K).boundaryFull (over K W) e := by
    rw [copy_inf_over, inf_eq_right.2 (boundary_le X e (!ε))]
    refine (?_ : copy K β W ≤ (partialCylinder U K).boundary (over K W) e β).trans
      (boundary_le_boundaryFull _ e β)
    simpa only [boundary_eq_self hdW.le β] using copy_boundary_le_boundary_over (K := K) W e β
  rw [inf_sup_right, inf_sup_right]
  refine sup_le (sup_le (hcopy (!ε)) ?_) (hcopy ε)
  rw [← over_inf]
  refine (over_mono hbW).trans ?_
  rcases Nat.eq_zero_or_pos e with rfl | hpos
  · rw [bdryFull, bdry_eq_bot hdW.le, bdry_eq_bot hdW.le, sup_bot_eq, over_bot]
    exact bot_le
  · obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    have hdW' : krullDim W = ((f + 1 : ℕ) : WithBot ℕ∞) := hdW
    rw [bdryFull, bdry_eq_boundary hdW', bdry_eq_boundary hdW', over_sup]
    exact sup_le
      ((over_boundary_le_boundary_over gW f true).trans (boundary_le_boundaryFull _ _ true))
      ((over_boundary_le_boundary_over gW f false).trans (boundary_le_boundaryFull _ _ false))

theorem krullDim_over_boundary_top {W : LowerSet U} {e : ℕ} (hWm : IsMoleculeIn U W)
    (hdW : krullDim W = e) (hKW : K ⊓ W ≤ U.bdryFull W) :
    krullDim (over K W) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  refine le_antisymm (krullDim_over_le hdW.le) ?_
  have hle (y : U) (hy : y ∈ W) : grade ℕ y ≤ e := krullDim_le_coe_iff.1 hdW.le ⟨y, hy⟩
  obtain ⟨y, hyW, hdy⟩ : ∃ y ∈ W, grade ℕ y = e := by
    rcases e with _ | f
    · obtain ⟨y, hyW⟩ := hWm.nonempty
      exact ⟨y, hyW, Nat.eq_zero_of_le_zero (hle y hyW)⟩
    · obtain ⟨⟨y, hyW⟩, hyf⟩ := coe_lt_krullDim_iff.1
        (show (f : WithBot ℕ∞) < krullDim W by rw [hdW]; exact_mod_cast Nat.lt_succ_self f)
      have h1 : f + 1 ≤ grade ℕ y := by exact_mod_cast hyf
      have h2 := hle y hyW
      exact ⟨y, hyW, by omega⟩
  have hyK : y ∉ K := fun hyK => by
    have hy := hKW ⟨hyK, hyW⟩
    rcases e with _ | f
    · rw [bdryFull, bdry_eq_bot hdW.le, bdry_eq_bot hdW.le, sup_bot_eq] at hy
      exact hy
    · have hdW' : krullDim W = ((f + 1 : ℕ) : WithBot ℕ∞) := hdW
      rw [bdryFull, bdry_eq_boundary hdW', bdry_eq_boundary hdW'] at hy
      have : grade ℕ y ≤ f := hy.elim grade_le_of_mem_boundary grade_le_of_mem_boundary
      omega
  have := grade_add_one_le_krullDim_over (K := K) hyW hyK
  rwa [hdy] at this

theorem halves_over_Iic_top (hU : IsMolecule U) {e : ℕ}
    (he : krullDim U = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hKU : K ≤ U.boundary ⊤ e ε) (hdx : grade ℕ x = e + 1) :
    IsMoleculeIn (invertedCylinder U K ε (e + 1))
        (copy K (!ε) (.Iic x) ⊔ over K (U.boundary (.Iic x) e ε) ⊔ copy K ε (.Iic x)) ∧
      IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K (U.boundary (.Iic x) e (!ε))) ∧
      (invertedCylinder U K ε (e + 1)).IsRound
        (copy K (!ε) (.Iic x) ⊔ over K (U.boundary (.Iic x) e ε) ⊔ copy K ε (.Iic x)) ∧
      (invertedCylinder U K ε (e + 1)).IsRound (over K (U.boundary (.Iic x) e (!ε))) ∧
      (∀ α, (invertedCylinder U K ε (e + 1)).bdry
          (copy K (!ε) (.Iic x) ⊔ over K (U.boundary (.Iic x) e ε) ⊔ copy K ε (.Iic x)) α =
        (partialCylinder U K).boundary (over K (U.boundary (.Iic x) e (!ε))) e α) ∧
      (∀ α, (invertedCylinder U K ε (e + 1)).bdry (over K (U.boundary (.Iic x) e (!ε))) α =
        (partialCylinder U K).boundary (over K (U.boundary (.Iic x) e (!ε))) e α) ∧
      (copy K (!ε) (.Iic x) ⊔ over K (U.boundary (.Iic x) e ε) ⊔ copy K ε (.Iic x)) ⊓
          over K (U.boundary (.Iic x) e (!ε)) =
        (partialCylinder U K).boundaryFull (over K (U.boundary (.Iic x) e (!ε))) e := by
  set X : LowerSet U := .Iic x with hXdef
  have hUle (w : U) : grade ℕ w ≤ e + 1 := krullDim_le_coe_iff.1 he.le w
  have hXa : U.IsAtomIn X := hU.isAtomIn_Iic trivial
  have hXm : IsMoleculeIn U X := hXa.isMoleculeIn
  have rX : U.IsRound X := hXa.isRound
  have gX := rX.isGlobular
  have hdX : krullDim X = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hXdef, LowerSet.krullDim_Iic, hdx]
  have hXU : U.IsSubmoleculeOf X ⊤ := hU.Iic_isSubmoleculeOf trivial
  have hKd := dim_lt_of_mem_K hKU
  have KX : K ⊓ X ≤ U.boundary X e ε := fun z hz => hXU.inf_boundary_le e ε ⟨hz.2, hKU hz.1⟩
  set W := U.boundary X e (!ε) with hWdef
  have hWm : IsMoleculeIn U W := hXm.boundary e (!ε)
  have rW : U.IsRound W := rX.boundary e (!ε)
  have hdW : krullDim W = e :=
    hXm.krullDim_boundary (by rw [hdX]; exact_mod_cast Nat.le_succ e) (!ε)
  have hbW : U.boundary X e ε ⊓ W ≤ U.bdryFull W := by
    have h := (rX.inf_boundary_eq_properBoundary hXm
      (by rw [hdX]; exact_mod_cast Nat.lt_succ_self e) (!ε)).trans hWm.properBoundary_eq_bdryFull
    rw [Bool.not_not, inf_comm] at h
    exact h.le
  have hKW : K ⊓ W ≤ U.bdryFull W := fun z hz =>
    hbW ⟨KX ⟨hz.1, boundary_le X e (!ε) hz.2⟩, hz.2⟩
  set F := copy K (!ε) X ⊔ over K (U.boundary X e ε) ⊔ copy K ε X with hFdef
  set G := over K W with hGdef
  have hFeq : (invertedCylinder U K ε (e + 1)).boundary (over K X) (e + 1) (!ε) = F := by
    rw [boundary_over_top_not hUle hKd, hFdef, sup_right_comm]
  obtain ⟨mF, -, bF1, bF2, rF⟩ := isMoleculeIn_front (K := K) hXU hdX hKU
  have hGstd : G ≤ std K ε (e + 1) := fun z hz => mem_std_of_dim_lt (by
    have := grade_le_of_mem_boundary (mem_over.1 hz); omega)
  have SW := cylinderStatement_of_isMoleculeIn (K := K) _ W rfl hWm
  have mG : IsMoleculeIn (invertedCylinder U K ε (e + 1)) G :=
    (isMoleculeIn_iff_of_subset_std hGstd).2 SW.1
  have rG : (invertedCylinder U K ε (e + 1)).IsRound G :=
    (round_iff_of_subset_std hGstd).2 (isRound_over rW hKW)
  have hdF : krullDim F = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    le_antisymm (hFeq ▸ krullDim_boundary_le (P := invertedCylinder U K ε (e + 1)) _ (e + 1) (!ε))
      (by rw [← hdX, ← krullDim_copy (K := K) ε X]; exact LowerSet.krullDim_mono le_sup_right)
  have hdG : krullDim G = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    krullDim_over_boundary_top hWm hdW hKW
  have keyG (α : Bool) : (invertedCylinder U K ε (e + 1)).bdry G α =
      (partialCylinder U K).boundary (over K W) e α := by
    rw [bdry_eq_boundary (P := invertedCylinder U K ε (e + 1)) hdG,
      boundary_eq_of_subset_std hGstd]
  have keyF' (α : Bool) : (invertedCylinder U K ε (e + 1)).boundary F e α =
      (partialCylinder U K).boundary (over K W) e α := by
    rcases Bool.eq_or_eq_not α ε with rfl | rfl
    · rw [bF2]; exact boundary_front_eps gX hKd
    · rw [bF1, boundary_over_boundary gX]
  have keyF (α : Bool) : (invertedCylinder U K ε (e + 1)).bdry F α =
      (partialCylinder U K).boundary (over K W) e α := by
    rw [bdry_eq_boundary (P := invertedCylinder U K ε (e + 1)) hdF, keyF']
  refine ⟨mF, mG, rF rX, rG, keyF, keyG,
    le_antisymm (front_inf_le gX hdW hbW) (sup_le ?_ ?_)⟩
  · exact le_inf (keyF' false ▸ boundary_le (P := invertedCylinder U K ε (e + 1)) F e false)
      (boundary_le (P := partialCylinder U K) G e false)
  · exact le_inf (keyF' true ▸ boundary_le (P := invertedCylinder U K ε (e + 1)) F e true)
      (boundary_le (P := partialCylinder U K) G e true)

theorem isMoleculeIn_over_Iic_top (hU : IsMolecule U) {e : ℕ}
    (he : krullDim U = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hKU : K ≤ U.boundary ⊤ e ε) (hx : x ∉ K) (hdx : grade ℕ x = e + 1) :
    IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K (.Iic x)) := by
  set X : LowerSet U := .Iic x
  have hUle (w : U) : grade ℕ w ≤ e + 1 := krullDim_le_coe_iff.1 he.le w
  have hKd := dim_lt_of_mem_K hKU
  have hKf := orient_eq_of_mem_K hKU
  set t := mkI K none x hx
  have ht : grade ℕ t = (e + 1) + 1 := by rw [grade_mkI_none, hdx]
  have hdS : krullDim (LowerSet.Iic t) = (((e + 1) + 1 : ℕ) : WithBot ℕ∞) := by
    rw [LowerSet.krullDim_Iic, ht]
  have hbF : (invertedCylinder U K ε (e + 1)).bdry (.Iic t) (!ε) =
      copy K (!ε) X ⊔ over K (U.boundary X e ε) ⊔ copy K ε X := by
    rw [bdry_eq_boundary (P := invertedCylinder U K ε (e + 1)) hdS, Iic_mkI_none hx,
      boundary_over_top_not hUle hKd, sup_right_comm]
  have hbG : (invertedCylinder U K ε (e + 1)).bdry (.Iic t) ε =
      over K (U.boundary X e (!ε)) := by
    rw [bdry_eq_boundary (P := invertedCylinder U K ε (e + 1)) hdS, Iic_mkI_none hx,
      boundary_over_top_eps hUle hKd hKf]
  obtain ⟨mF, mG, rF, rG, keyF, keyG, hFG⟩ := halves_over_Iic_top (K := K) hU he hKU hdx
  have hbdry (α : Bool) : IsMoleculeIn (invertedCylinder U K ε (e + 1))
      ((invertedCylinder U K ε (e + 1)).bdry (.Iic t) α) := by
    rcases Bool.eq_or_eq_not α ε with rfl | rfl
    · rwa [hbG]
    · rwa [hbF]
  have hr (α : Bool) : (invertedCylinder U K ε (e + 1)).IsRound
      ((invertedCylinder U K ε (e + 1)).bdry (.Iic t) α) := by
    rcases Bool.eq_or_eq_not α ε with rfl | rfl
    · rwa [hbG]
    · rwa [hbF]
  have hbd_eq (γ α : Bool) :
      (invertedCylinder U K ε (e + 1)).bdry ((invertedCylinder U K ε (e + 1)).bdry (.Iic t) γ) α =
        (partialCylinder U K).boundary (over K (U.boundary X e (!ε))) e α := by
    rcases Bool.eq_or_eq_not γ ε with rfl | rfl
    · rw [hbG, keyG]
    · rw [hbF, keyF]
  rw [← Iic_mkI_none hx]
  refine IsMoleculeIn.atom (P := invertedCylinder U K ε (e + 1)) t
    (isRound_Iic_of_halves ht (fun α => (hbdry α).nonempty) hr
      (fun α => (hbd_eq false α).trans (hbd_eq true α).symm) ?_) hbdry
  rw [bdryFull, hbd_eq false false, hbd_eq false true, ← boundaryFull, ← hFG]
  cases ε
  · rw [Bool.not_false] at hbF; rw [hbG, hbF, inf_comm]; rfl
  · rw [Bool.not_true] at hbF; rw [hbF, hbG]; rfl

theorem isMoleculeIn_over_of_isPastingIn_lt {V W W' : LowerSet U} {k e : ℕ}
    (he : krullDim U = ((e + 1 : ℕ) : WithBot ℕ∞)) (hKU : K ≤ U.boundary ⊤ e ε)
    (hp : U.IsPastingIn k W W' V) (hV : IsMoleculeIn U V) (hW : IsMoleculeIn U W)
    (hW' : IsMoleculeIn U W') (hk : (k : WithBot ℕ∞) < min (krullDim W) (krullDim W'))
    (hke : k < e)
    (mW : IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K W))
    (mW' : IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K W')) :
    IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K V) := by
  have hUle (w : U) : grade ℕ w ≤ e + 1 := krullDim_le_coe_iff.1 he.le w
  have hKd := dim_lt_of_mem_K hKU
  have hKf := orient_eq_of_mem_K hKU
  have gV := hV.isGlobular
  have gW := hW.isGlobular
  have gW' := hW'.isGlobular
  set DV := U.boundary V e (!ε) with hDV
  set DW := U.boundary W e (!ε) with hDW
  set DW' := U.boundary W' e (!ε) with hDW'
  have hpD : U.IsPastingIn k DW DW' DV := hp.boundary_of_lt gW gW' hke (!ε)
  have mDV : IsMoleculeIn U DV := hV.boundary e (!ε)
  have mDW : IsMoleculeIn U DW := hW.boundary e (!ε)
  have mDW' : IsMoleculeIn U DW' := hW'.boundary e (!ε)
  have hdD (Y : LowerSet U) (hY : IsMoleculeIn U Y) (hkY : (k : WithBot ℕ∞) < krullDim Y) :
      (k : WithBot ℕ∞) < krullDim (U.boundary Y e (!ε)) := by
    rcases le_total (krullDim Y) e with h | h
    · rw [boundary_eq_self h]; exact hkY
    · rw [hY.krullDim_boundary h]; exact_mod_cast hke
  have hkD : (k : WithBot ℕ∞) < min (krullDim DW) (krullDim DW') :=
    lt_min (hdD W hW (lt_min_iff.1 hk).1) (hdD W' hW' (lt_min_iff.1 hk).2)
  have sD : DW < DV := hpD.lt_cond false (hkD.trans_le (min_le_right _ _))
  have sD' : DW' < DV := hpD.lt_cond true (hkD.trans_le (min_le_left _ _))
  obtain ⟨c1, c2, c4, c5, c6, c7⟩ := genPastingConditions_over_of_isPastingIn (K := K) hpD mDV
    mDW mDW' sD sD' hkD fun X _ hmX => cylinderStatement_of_isMoleculeIn _ X rfl hmX
  have hb {Y : LowerSet U} (gY : U.IsGlobular Y) (γ : Bool) :
      (invertedCylinder U K ε (e + 1)).boundary (over K Y) (k + 1) γ =
        (partialCylinder U K).boundary (over K (U.boundary Y e (!ε))) (k + 1) γ :=
    boundary_over_eq_boundary_over_bdry gY hUle (by omega) (by omega) hKd hKf γ
  have hstd (Y : LowerSet U) (γ : Bool) :
      (partialCylinder U K).boundary (over K Y) (k + 1) γ ≤ std K ε (e + 1) :=
    subset_std_of_dimOf_lt (lt_of_le_of_lt
      (krullDim_boundary_le (P := partialCylinder U K) _ (k + 1) γ)
      (by exact_mod_cast Nat.succ_lt_succ hke))
  have hWW' : W ⊓ W' = DW ⊓ DW' := by
    rw [hp.inf_eq_output, hpD.inf_eq_output, hDW, gW k e hke true (!ε)]
  have hfac {A B DA DB : LowerSet U} (hs : DA ⊔ DB = DV) (hAB : A ⊓ B = DA ⊓ DB) (hA : DA ≤ A)
      (hB : DB ≤ B) : B ⊓ DV = DB := by
    rw [← hs, inf_sup_left, inf_eq_right.2 hB]
    exact sup_eq_right.2
      ((le_inf (inf_le_right.trans hA) inf_le_left).trans (hAB.le.trans inf_le_right))
  have hs {Y DY : LowerSet U} (hY : Y ⊓ DV = DY) (γ : Bool) :
      over K Y ⊓ (partialCylinder U K).boundary (over K DV) (k + 1) γ =
        over K DY ⊓ (partialCylinder U K).boundary (over K DV) (k + 1) γ := by
    rw [← hY, over_inf, inf_assoc,
      inf_eq_right.2 (boundary_le (P := partialCylinder U K) (over K DV) (k + 1) γ)]
  have h5s := hs (hfac hpD.sup_eq hWW' (boundary_le _ _ _) (boundary_le _ _ _))
  have h6s := hs (hfac ((sup_comm _ _).trans hpD.sup_eq) (by rw [inf_comm, hWW', inf_comm])
    (boundary_le _ _ _) (boundary_le _ _ _))
  have hAB : over K W' ⊓ over K W = over K DW' ⊓ over K DW := by
    rw [← over_inf, ← over_inf, inf_comm W' W, inf_comm DW' DW, hWW']
  have hE : over K W' ⊔ over K W = over K V := by
    rw [← over_sup, sup_comm, hp.sup_eq]
  rw [← hE]
  refine IsGenPastingIn.isMoleculeIn (P := invertedCylinder U K ε (e + 1)) (k := k + 1)
    ⟨mW', mW, ?_, ?_, ?_, ?_⟩ ?_ ?_
  · rw [hb gW', hAB]; exact isSubmoleculeOf_of_subset_std (hstd _ _) c1
  · rw [hb gW, hAB]; exact isSubmoleculeOf_of_subset_std (hstd _ _) c2
  · rw [hE, hb gV, hb gW']; exact isSubmoleculeOf_of_subset_std (hstd _ _) c4
  · rw [hE, hb gV, hb gW]; exact isSubmoleculeOf_of_subset_std (hstd _ _) c5
  · rw [hE, hb gV, hb gW', h5s]; exact c6
  · rw [hE, hb gV, hb gW, h6s]; exact c7

theorem isMoleculeIn_over_sup_top {e : ℕ}
    (he : krullDim U = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hKU : K ≤ U.boundary ⊤ e ε) {X Y : LowerSet U}
    (hYU : U.IsSubmoleculeOf Y ⊤)
    (hdY : krullDim Y = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hXY : X ⊓ Y = U.boundary X e (!ε))
    (hYX : X ⊓ Y = U.boundary Y e ε)
    (mX : IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K X))
    (mY : IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K Y)) :
    IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K (Y ⊔ X)) := by
  have hUle (w : U) : grade ℕ w ≤ e + 1 := krullDim_le_coe_iff.1 he.le w
  have hKd := dim_lt_of_mem_K hKU
  have hKf := orient_eq_of_mem_K hKU
  obtain ⟨-, sF, -, -, -⟩ := isMoleculeIn_front (K := K) hYU hdY hKU
  have hF : (invertedCylinder U K ε (e + 1)).boundary (over K Y) (e + 1) (!ε) =
      copy K (!ε) Y ⊔ over K (U.boundary Y e ε) ⊔ copy K ε Y := by
    rw [boundary_over_top_not hUle hKd, sup_right_comm]
  have hG : (invertedCylinder U K ε (e + 1)).boundary (over K X) (e + 1) (!(!ε)) =
      over K (U.boundary X e (!ε)) := by
    rw [Bool.not_not]; exact boundary_over_top_eps hUle hKd hKf
  have hsub : (invertedCylinder U K ε (e + 1)).IsSubmoleculeOf
      ((invertedCylinder U K ε (e + 1)).boundary (over K X) (e + 1) (!(!ε)))
      ((invertedCylinder U K ε (e + 1)).boundary (over K Y) (e + 1) (!ε)) := by
    rw [hG, hF, ← hXY, hYX]; exact sF
  have hint : over K Y ⊓ over K X =
      (invertedCylinder U K ε (e + 1)).boundary (over K X) (e + 1) (!(!ε)) := by
    rw [hG, ← over_inf, inf_comm, hXY]
  rw [over_sup]
  exact (isMoleculeIn_sup_of_isSubmoleculeOf_boundary_boundary mY mX hsub hint).1

theorem isMoleculeIn_over_of_isSubmoleculeOf (hU : IsMolecule U) {e : ℕ}
    (he : krullDim U = ((e + 1 : ℕ) : WithBot ℕ∞)) (hKU : K ≤ U.boundary ⊤ e ε) {V : LowerSet U}
    (hV : IsMoleculeIn U V) :
    U.IsSubmoleculeOf V ⊤ → IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K V) := by
  have hKd := dim_lt_of_mem_K hKU
  have low (V : LowerSet U) (hV : IsMoleculeIn U V) (hd : krullDim V ≤ e) :
      IsMoleculeIn (invertedCylinder U K ε (e + 1)) (over K V) := by
    have hstd : over K V ≤ std K ε (e + 1) := fun z hz => mem_std_of_dim_lt (by
      have : grade ℕ (partialCylinderProj U K z) ≤ e :=
        krullDim_le_coe_iff.1 hd ⟨_, mem_over.1 hz⟩
      omega)
    exact (isMoleculeIn_iff_of_subset_std hstd).2 (isMoleculeIn_over hV)
  have top (V : LowerSet U) (hV : IsMoleculeIn U V) (hd : ¬ krullDim V ≤ e) :
      krullDim V = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    obtain ⟨d, hd'⟩ := hV.exists_krullDim_eq
    have htop : krullDim (⊤ : LowerSet U) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
      rw [LowerSet.krullDim_top, he]
    have hle : krullDim V ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
      (LowerSet.krullDim_mono (le_top : V ≤ ⊤)).trans htop.le
    rw [hd'] at hd hle ⊢
    norm_cast at hd hle ⊢
    omega
  induction hV with
  | point x hx =>
    refine fun _ => low _ (.point x hx) ?_
    rw [LowerSet.krullDim_Iic_of_isMin hx]
    exact_mod_cast Nat.zero_le e
  | atom t hr hbdry _ =>
    intro _
    by_cases hd : krullDim (LowerSet.Iic t) ≤ e
    · exact low _ (.atom t hr hbdry) hd
    have hdV := top _ (.atom t hr hbdry) hd
    have hdt : grade ℕ t = e + 1 := by
      rw [LowerSet.krullDim_Iic] at hdV
      exact_mod_cast hdV
    have htK : t ∉ K := fun h => by have := hKd t h; omega
    exact isMoleculeIn_over_Iic_top hU he hKU htK hdt
  | paste k W W' V hp hW hW' hk ihW ihW' =>
    intro hVU
    have hV := IsMoleculeIn.paste k W W' V hp hW hW' hk
    by_cases hd : krullDim V ≤ e
    · exact low _ hV hd
    have hdV := top V hV hd
    have hWU : U.IsSubmoleculeOf W ⊤ :=
      (hp.isPastingFactorOf false hW hW').isSubmoleculeOf.trans hVU
    have hW'U : U.IsSubmoleculeOf W' ⊤ :=
      (hp.isPastingFactorOf true hW' hW).isSubmoleculeOf.trans hVU
    have mW := ihW hWU
    have mW' := ihW' hW'U
    rcases Nat.lt_or_ge k e with hke | hke
    · exact isMoleculeIn_over_of_isPastingIn_lt he hKU hp hV hW hW' hk hke mW mW'
    · have hkW : (k : WithBot ℕ∞) < krullDim W := (lt_min_iff.1 hk).1
      have hkW' : (k : WithBot ℕ∞) < krullDim W' := (lt_min_iff.1 hk).2
      have hWd : krullDim W ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := hdV ▸ LowerSet.krullDim_mono hp.left_le
      have hW'd : krullDim W' ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
        hdV ▸ LowerSet.krullDim_mono hp.right_le
      obtain ⟨dW, hdW⟩ := hW.exists_krullDim_eq
      obtain ⟨dW', hdW'⟩ := hW'.exists_krullDim_eq
      rw [hdW] at hkW hWd
      rw [hdW'] at hkW' hW'd
      norm_cast at hkW hWd hkW' hW'd
      obtain rfl : k = e := by omega
      have hdW_eq : krullDim W = ((k + 1 : ℕ) : WithBot ℕ∞) := by
        rw [hdW]; exact_mod_cast (by omega)
      have hdW'_eq : krullDim W' = ((k + 1 : ℕ) : WithBot ℕ∞) := by
        rw [hdW']; exact_mod_cast (by omega)
      cases ε
      · have h := isMoleculeIn_over_sup_top (ε := false) he hKU hW'U hdW'_eq
          hp.inf_eq_output hp.inf_eq_input mW mW'
        rwa [sup_comm, hp.sup_eq] at h
      · have h := isMoleculeIn_over_sup_top (ε := true) he hKU hWU hdW_eq
          (inf_comm W' W ▸ hp.inf_eq_input) (inf_comm W' W ▸ hp.inf_eq_output) mW' mW
        rwa [hp.sup_eq] at h

theorem isMolecule_invertedCylinder {U : OGP.{u}} (hU : IsMolecule U) {n : ℕ}
    (hn : krullDim U = n) (hpos : 0 < n) {K : LowerSet U} {ε : Bool}
    (hKU : K ≤ U.bdry ⊤ ε) :
    IsMolecule (invertedCylinder U K ε n) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  have htop : krullDim (⊤ : LowerSet U) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [LowerSet.krullDim_top, hn]
  have h := isMoleculeIn_over_of_isSubmoleculeOf hU hn
    (hKU.trans (bdry_eq_boundary htop ε).le) hU (.refl hU)
  rwa [over_top] at h

theorem isRound_invertedCylinder {U : OGP.{u}} (hU : IsMolecule U) {n : ℕ}
    (hn : krullDim U = n) (hpos : 0 < n) (hr : U.IsRound ⊤) {K : LowerSet U} {ε : Bool}
    (hKU : K ≤ U.bdry ⊤ ε) : (invertedCylinder U K ε n).IsRound ⊤ := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  have hdU : krullDim (⊤ : LowerSet U) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [LowerSet.krullDim_top, hn]
  have hUle (w : U) : grade ℕ w ≤ e + 1 := krullDim_le_coe_iff.1 hn.le w
  have hKU' : K ≤ U.boundary ⊤ e ε := hKU.trans (bdry_eq_boundary hdU ε).le
  have hKd := dim_lt_of_mem_K hKU'
  have hKf := orient_eq_of_mem_K hKU'
  have hL := isMolecule_invertedCylinder hU hn hpos hKU
  have gL := hL.isGlobular
  have gU := hr.isGlobular
  set D := U.boundary ⊤ e (!ε) with hDdef
  have hDm : IsMoleculeIn U D := hU.boundary e (!ε)
  have rD : U.IsRound D := hr.boundary e (!ε)
  have hdD : krullDim D = e := hU.krullDim_boundary (by rw [hdU]; exact_mod_cast Nat.le_succ e) (!ε)
  have hbW : U.boundary ⊤ e ε ⊓ D ≤ U.bdryFull D := by
    have h := (hr.inf_boundary_eq_properBoundary hU
      (by rw [hdU]; exact_mod_cast Nat.lt_succ_self e) (!ε)).trans hDm.properBoundary_eq_bdryFull
    rw [Bool.not_not, inf_comm] at h
    exact h.le
  have hKD : K ⊓ D ≤ U.bdryFull D := fun z hz => hbW ⟨hKU' hz.1, hz.2⟩
  have rOD := isRound_over (K := K) rD hKD
  have hDstd : over K D ≤ std K ε (e + 1) := fun z hz => mem_std_of_dim_lt (by
    have := grade_le_of_mem_boundary (mem_over.1 hz); omega)
  have htopε : (invertedCylinder U K ε (e + 1)).boundary ⊤ (e + 1) ε = over K D := by
    rw [← over_top (K := K)]; exact boundary_over_top_eps hUle hKd hKf
  have htopn : (invertedCylinder U K ε (e + 1)).boundary ⊤ (e + 1) (!ε) =
      copy K (!ε) ⊤ ⊔ over K (U.boundary ⊤ e ε) ⊔ copy K ε ⊤ := by
    rw [← over_top (K := K), boundary_over_top_not hUle hKd, sup_right_comm]
  have hlow (j : ℕ) (hj : j ≤ e) (α : Bool) :
      (invertedCylinder U K ε (e + 1)).boundary ⊤ j α =
        (partialCylinder U K).boundary (over K D) j α := by
    rw [← gL j (e + 1) (Nat.lt_succ_of_le hj) α ε, htopε, boundary_eq_of_subset_std hDstd]
  have hdL :
      krullDim (⊤ : LowerSet (invertedCylinder U K ε (e + 1))) = ((e + 2 : ℕ) : WithBot ℕ∞) :=
    over_top (K := K) ▸ krullDim_over_top hKd hdU
  have hdOD : krullDim (over K D) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    krullDim_over_boundary_top hDm hdD hKD
  refine ⟨gL, fun _ => ?_, fun m hm => ?_⟩
  · rw [hlow 0 (Nat.zero_le e), hlow 0 (Nat.zero_le e)]
    exact rOD.inf_boundary_zero (by rw [hdOD]; exact_mod_cast Nat.succ_pos e)
  · have hme : m ≤ e := by
      rw [hdL] at hm
      norm_cast at hm
      omega
    rcases hme.lt_or_eq with hlt | rfl
    · rw [hlow (m + 1) hlt, hlow (m + 1) hlt, boundaryFull, hlow m hlt.le, hlow m hlt.le]
      exact rOD.inf_boundary_succ m (by rw [hdOD]; exact_mod_cast Nat.succ_lt_succ hlt)
    · refine le_antisymm ?_ (sup_le
        (le_inf (gL.boundary_le_boundary (Nat.lt_succ_self m) _ _)
          (gL.boundary_le_boundary (Nat.lt_succ_self m) _ _))
        (le_inf (gL.boundary_le_boundary (Nat.lt_succ_self m) _ _)
          (gL.boundary_le_boundary (Nat.lt_succ_self m) _ _)))
      rw [boundaryFull, hlow m le_rfl, hlow m le_rfl, ← boundaryFull]
      have hc : (invertedCylinder U K ε (m + 1)).boundary ⊤ (m + 1) false ⊓
          (invertedCylinder U K ε (m + 1)).boundary ⊤ (m + 1) true =
          (copy K (!ε) ⊤ ⊔ over K (U.boundary ⊤ m ε) ⊔ copy K ε ⊤) ⊓ over K D := by
        cases ε
        · rw [Bool.not_false] at htopn; rw [htopε, htopn, inf_comm]; rfl
        · rw [Bool.not_true] at htopn; rw [htopn, htopε]; rfl
      rw [hc]
      exact front_inf_le gU hdD hbW

theorem isAtom_invertedCylinder {U : OGP.{u}} (hU : IsAtom U) {n : ℕ}
    (hn : krullDim U = n) (hd : 0 < n) {K : LowerSet U} {ε : Bool} (hKU : K ≤ U.bdry ⊤ ε) :
    IsAtom (invertedCylinder U K ε n) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  have hdU : krullDim (⊤ : LowerSet U) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [LowerSet.krullDim_top, hn]
  have hKd := dim_lt_of_mem_K (hKU.trans (bdry_eq_boundary hdU ε).le)
  obtain ⟨t, ht⟩ := hU.2
  have htop (x : U) : x ≤ t := LowerSet.mem_Iic_iff.1 (ht ▸ trivial)
  have hdt : grade ℕ t = e + 1 := by
    have h1 : krullDim (⊤ : LowerSet U) = ((grade ℕ t : ℕ) : WithBot ℕ∞) := by
      rw [ht, LowerSet.krullDim_Iic]
    exact_mod_cast h1.symm.trans hdU
  have htK : t ∉ K := fun h => by have := hKd t h; omega
  exact ⟨isMolecule_invertedCylinder hU.1 hn hd hKU, mkI K none t htK,
    SetLike.ext fun a => ⟨fun _ => le_mkI_none_of_proj_le htK (htop _), fun _ => trivial⟩⟩

end InvertedCylinder

end Atoms.Molecule.OGP
