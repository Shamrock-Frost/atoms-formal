import Atoms.Molecule.RegularComplex.Thin
import Atoms.Molecule.Layering.Interior

universe u v

open Order Set Topology

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}} {f : P → Q}

theorem IsMorphism.apply_lt_apply (hf : IsMorphism f) {a b : P} (h : a < b) :
    f a < f b :=
  lt_of_le_of_ne (hf.monotone h.le) fun e =>
    (grade_strictMono (𝕆 := ℕ) h).ne (by rw [← hf.grade_eq a, ← hf.grade_eq b, e])

theorem IsMorphism.eq_of_covBy_of_apply_eq (hf : IsMorphism f) {x y z : P}
    (hx : x ⋖ z) (hy : y ⋖ z) (h : f x = f y) : x = y := by
  have e : P.orient hx = P.orient hy := by
    rw [← hf.orient_apply hx, ← hf.orient_apply hy]
    exact Q.orient_congr rfl h (hf.covBy_apply hx) (hf.covBy_apply hy)
  exact (hf.bijOn_faces z (P.orient hy)).injOn ⟨hx, e⟩ ⟨hy, rfl⟩ h

theorem IsMorphism.image_Iic (hf : IsMorphism f) (x : P) :
    f '' (LowerSet.Iic x : Set P) = LowerSet.Iic (f x) :=
  (Relation.fibration_iff_image_Iic hf.monotone).1 hf.fibration x

theorem mem_interior_boundary_Iic_orient_of_covBy {A : LowerSet P}
    (hA : IsMoleculeIn P A) {x y : P} (hy : y ∈ A) (hxy : x ⋖ y) :
    x ∈ P.interior (P.boundary (.Iic y) (grade ℕ y - 1) (P.orient hxy)) := by
  have hdxy := Nat.covBy_iff_add_one_eq.1 (hxy.grade ℕ)
  have hB := (hA.isAtomIn_Iic hy).isMoleculeIn
  have hmem : x ∈ P.boundary (.Iic y) (grade ℕ y - 1) (P.orient hxy) := by
    rw [boundary_Iic (by omega : grade ℕ y = (grade ℕ y - 1) + 1)]
    exact subset_lowerClosure ⟨hxy, rfl⟩
  have hdB : krullDim (P.boundary (.Iic y) (grade ℕ y - 1) (P.orient hxy)) =
      (grade ℕ y - 1 : ℕ) :=
    hB.krullDim_boundary (by rw [LowerSet.krullDim_Iic]; exact_mod_cast (by omega)) _
  refine (mem_interior_iff_of_isMoleculeIn (hB.boundary _ _) hmem).2 (Or.inl ?_)
  rw [hdB]
  exact_mod_cast (by omega : grade ℕ x = grade ℕ y - 1)

theorem orient_eq_of_mem_interior_boundary_Iic {A : LowerSet P}
    (hA : IsMoleculeIn P A) {x y : P} (hy : y ∈ A) (hxy : x ⋖ y) {α : Bool}
    (hx : x ∈ P.interior (P.boundary (.Iic y) (grade ℕ y - 1) α)) :
    P.orient hxy = α := by
  by_contra hne
  have h1 := mem_interior_boundary_Iic_orient_of_covBy hA hy hxy
  rw [Bool.eq_not_of_ne hne] at h1
  have hpos : 0 < grade ℕ y := by have := Nat.covBy_iff_add_one_eq.1 (hxy.grade ℕ); omega
  exact notMem_interior_boundary_Iic hA hy hpos α (P.interior_subset _ hx)
    (P.interior_subset _ h1) hx

theorem eq_of_covBy_of_orient_eq {A : LowerSet P} (hA : IsMoleculeIn P A)
    {x y y' : P} (hy : y ∈ A) (hy' : y' ∈ A)
    (hyd : (grade ℕ y : WithBot ℕ∞) = krullDim A)
    (hy'd : (grade ℕ y' : WithBot ℕ∞) = krullDim A)
    (hxy : x ⋖ y) (hxy' : x ⋖ y')
    (ho : P.orient hxy = P.orient hxy') : y = y' := by
  have h' := mem_interior_boundary_Iic_orient_of_covBy hA hy' hxy'
  rw [← ho] at h'
  exact eq_of_mem_interior_boundary_Iic hA hy hy' hyd hy'd _
    (mem_interior_boundary_Iic_orient_of_covBy hA hy hxy) h'

theorem exists_pair_covBy_of_mem_interior {A : LowerSet P} (hA : IsMoleculeIn P A)
    {x : P} (hx : x ∈ P.interior A) (hxd : ((grade ℕ x + 1 : ℕ) : WithBot ℕ∞) = krullDim A) :
    ∃ y₁ y₂ : P, y₁ ≠ y₂ ∧ ∀ y, (y ∈ A ∧ x ⋖ y) ↔ (y = y₁ ∨ y = y₂) := by
  have hxA := P.interior_subset _ hx
  rcases (mem_interior_iff_of_isMoleculeIn hA hxA).1 hx with h | ⟨-, yp, hyp, ym, hym, hpd, hmd,
    hp, hm⟩
  · have : grade ℕ x = grade ℕ x + 1 := by exact_mod_cast h.trans hxd.symm
    omega
  have hcov : ∀ {z : P} {α : Bool}, (grade ℕ z : WithBot ℕ∞) = krullDim A →
      x ∈ P.interior (P.boundary (.Iic z) (grade ℕ z - 1) α) → x ⋖ z := by
    intro z α hzd hz
    have hle : x ≤ z := boundary_le (.Iic z) _ _ (P.interior_subset _ hz)
    have hgz : grade ℕ z = grade ℕ x + 1 := by exact_mod_cast hzd.trans hxd.symm
    exact GradeOrder.covBy_of_le_of_grade_eq_add_one hle hgz
  have hcp := hcov hpd hp
  have hcm := hcov hmd hm
  have hop := orient_eq_of_mem_interior_boundary_Iic hA hyp hcp hp
  have hom := orient_eq_of_mem_interior_boundary_Iic hA hym hcm hm
  refine ⟨yp, ym, fun e => ?_, fun y => ⟨fun ⟨hy, hxy⟩ => ?_,
    fun h => h.elim (· ▸ ⟨hyp, hcp⟩) (· ▸ ⟨hym, hcm⟩)⟩⟩
  · subst e
    exact Bool.noConfusion (hop.symm.trans hom)
  · have hyd : (grade ℕ y : WithBot ℕ∞) = krullDim A := by
      rw [← hxd]
      exact_mod_cast (Nat.covBy_iff_add_one_eq.1 (hxy.grade ℕ)).symm
    cases ho : P.orient hxy
    · exact Or.inr (eq_of_covBy_of_orient_eq hA hy hym hyd hmd hxy hcm (ho.trans hom.symm))
    · exact Or.inl (eq_of_covBy_of_orient_eq hA hy hyp hyd hpd hxy hcp (ho.trans hop.symm))

theorem existsUnique_covBy_of_mem_bdryFull {A : LowerSet P} (hA : IsMoleculeIn P A)
    (hr : P.IsRound A) {x : P} (hx : x ∈ P.bdryFull A)
    (hxd : ((grade ℕ x + 1 : ℕ) : WithBot ℕ∞) = krullDim A) :
    ∃ y₀ : P, ∀ y, (y ∈ A ∧ x ⋖ y) ↔ y = y₀ := by
  have hAd : krullDim A = grade ℕ x + 1 := by rw [← hxd]; push_cast; rfl
  rw [bdryFull, bdry_eq_boundary hAd, bdry_eq_boundary hAd, ← boundaryFull] at hx
  obtain ⟨β, hxβ⟩ := mem_boundaryFull.1 hx
  have hor : ∀ y ∈ A, ∀ hxy : x ⋖ y,
      (grade ℕ y : WithBot ℕ∞) = krullDim A ∧ P.orient hxy = β := by
    intro y hy hxy
    have hyd' : grade ℕ y = grade ℕ x + 1 := (Nat.covBy_iff_add_one_eq.1 (hxy.grade ℕ)).symm
    refine ⟨by rw [← hxd]; exact_mod_cast hyd', ?_⟩
    have hn := notMem_boundary_of_mem_interior_boundary_Iic hA hy (by omega) _
      (mem_interior_boundary_Iic_orient_of_covBy hA hy hxy)
    rw [hyd', Nat.add_sub_cancel] at hn
    revert hn hxβ
    cases P.orient hxy <;> cases β <;> simp
  obtain ⟨m, hxm, hm⟩ := hA.exists_le_maximal (boundary_le A _ _ hxβ)
  have hmd' : grade ℕ m = grade ℕ x + 1 := hr.grade_eq_of_maximal hxd.symm hm
  have hxm' : x ⋖ m := GradeOrder.covBy_of_le_of_grade_eq_add_one hxm hmd'
  refine ⟨m, fun y => ⟨fun ⟨hy, hxy⟩ => ?_, fun h => h ▸ ⟨hm.prop, hxm'⟩⟩⟩
  obtain ⟨hyd, hyo⟩ := hor y hy hxy
  exact eq_of_covBy_of_orient_eq hA hy hm.prop hyd (hor m hm.prop hxm').1 hxy hxm'
    (hyo.trans (hor m hm.prop hxm').2.symm)

theorem exists_pair_covBy_of_mem_boundaryFull_of_isAtomIn {U : LowerSet P}
    (hU : P.IsAtomIn U) {k : ℕ} (hk : (k : WithBot ℕ∞) < krullDim U) {x : P}
    (hx : x ∈ P.boundaryFull U k) (hxd : grade ℕ x + 1 = k) :
    ∃ y₁ y₂ : P, y₁ ≠ y₂ ∧
      ∀ y, (y ∈ P.boundaryFull U k ∧ x ⋖ y) ↔ (y = y₁ ∨ y = y₂) := by
  have hUm := hU.isMoleculeIn
  have hr := hU.isRound
  have hBm : ∀ α, IsMoleculeIn P (P.boundary U k α) := hUm.boundary k
  have hBd : ∀ α, krullDim (P.boundary U k α) = (k : ℕ) := hUm.krullDim_boundary hk.le
  have hBr : ∀ α, P.IsRound (P.boundary U k α) := hr.boundary k
  have hI : P.boundary U k false ⊓ P.boundary U k true = P.boundaryFull U (grade ℕ x) :=
    hxd ▸ hr.inf_boundary_succ (grade ℕ x) (by exact_mod_cast hxd ▸ hk)
  have hbd : ∀ (α : Bool) (z : P), z ∈ P.bdryFull (P.boundary U k α) ↔
      ∀ β, z ∈ P.boundary U k β := fun α z => by
    rw [← (hBm α).properBoundary_eq_bdryFull, ← hr.inf_boundary_eq_properBoundary hUm hk α,
      LowerSet.mem_inf_iff, Bool.forall_bool' α]
  have hnot : ∀ y, y ∈ P.boundary U k true → y ∈ P.boundary U k false → grade ℕ y < k := by
    intro y h1 h2
    obtain ⟨_, hy⟩ := mem_boundaryFull.1 (hI ▸ ⟨h2, h1⟩ : y ∈ P.boundaryFull U (grade ℕ x))
    have := grade_le_of_mem_boundary hy
    omega
  by_cases hb : ∀ β, x ∈ P.boundary U k β
  · obtain ⟨yt, hyt⟩ := existsUnique_covBy_of_mem_bdryFull (hBm true) (hBr true)
      ((hbd true x).2 hb) (by rw [hBd]; exact_mod_cast hxd)
    obtain ⟨yf, hyf⟩ := existsUnique_covBy_of_mem_bdryFull (hBm false) (hBr false)
      ((hbd false x).2 hb) (by rw [hBd]; exact_mod_cast hxd)
    have hytm := (hyt yt).2 rfl
    have hyfm := (hyf yf).2 rfl
    refine ⟨yt, yf, fun e => ?_, fun y => ?_⟩
    · have h1 := hnot yt hytm.1 (by rw [e]; exact hyfm.1)
      have h2 := Nat.covBy_iff_add_one_eq.1 (hytm.2.grade ℕ)
      omega
    · rw [boundaryFull, LowerSet.mem_sup_iff]
      constructor
      · rintro ⟨hy | hy, hxy⟩
        exacts [Or.inr ((hyf y).1 ⟨hy, hxy⟩), Or.inl ((hyt y).1 ⟨hy, hxy⟩)]
      · rintro (rfl | rfl)
        exacts [⟨Or.inr hytm.1, hytm.2⟩, ⟨Or.inl hyfm.1, hyfm.2⟩]
  · have key : ∀ α : Bool, x ∈ P.boundary U k α → x ∉ P.boundary U k (!α) →
        ∃ y₁ y₂ : P, y₁ ≠ y₂ ∧
          ∀ y, (y ∈ P.boundaryFull U k ∧ x ⋖ y) ↔ (y = y₁ ∨ y = y₂) := by
      intro α hxα hxn
      have hint : x ∈ P.interior (P.boundary U k α) :=
        ⟨hxα, fun h => hb ((hbd α x).1 ((hBm α).properBoundary_eq_bdryFull ▸ h))⟩
      obtain ⟨y₁, y₂, hne, hiff⟩ :=
        exists_pair_covBy_of_mem_interior (hBm α) hint (by rw [hBd]; exact_mod_cast hxd)
      refine ⟨y₁, y₂, hne, fun y => ?_⟩
      rw [← hiff y]
      refine ⟨fun ⟨hy, hxy⟩ => ⟨?_, hxy⟩, fun ⟨hy, hxy⟩ =>
        ⟨boundary_le_boundaryFull U k α hy, hxy⟩⟩
      obtain ⟨β, hy⟩ := mem_boundaryFull.1 hy
      by_cases hβ : β = α
      · exact hβ ▸ hy
      · exact absurd ((P.boundary U k β).lower hxy.le hy) (Bool.eq_not_of_ne hβ ▸ hxn)
    obtain ⟨α, hx⟩ := mem_boundaryFull.1 hx
    exact key α hx fun h => hb ((Bool.forall_bool' α).2 ⟨hx, h⟩)

theorem boundary_eq_lowerClosure_facesIn_of_isRound {A : LowerSet P} (hr : P.IsRound A) {n j : ℕ}
    (hA : krullDim A = n) (hj : j < n) (α : Bool) :
    P.boundary A j α = lowerClosure (P.facesIn A j α) := by
  rw [boundary]
  congr 1
  refine Set.union_eq_left.2 fun m ⟨hm, hmj⟩ => ?_
  have := hr.grade_eq_of_maximal hA hm
  omega

theorem boundaryFull_le_boundaryFull_succ {U : LowerSet P}
    (hg : P.IsGlobular U) (k : ℕ) : P.boundaryFull U k ≤ P.boundaryFull U (k + 1) :=
  sup_le_sup (hg.boundary_le_boundary (Nat.lt_succ_self k) _ _)
    (hg.boundary_le_boundary (Nat.lt_succ_self k) _ _)

theorem IsMorphism.apply_eq_of_image_Iic_subset (hf : IsMorphism f) {t : P}
    {s : Q} (hUV : f '' (LowerSet.Iic t : Set P) ⊆ LowerSet.Iic s) (hd : grade ℕ t = grade ℕ s) :
    f t = s :=
  GradeOrder.eq_of_le_of_grade_le
    (hUV (mem_image_of_mem f (LowerSet.mem_Iic_iff.2 le_rfl)))
    ((hf.grade_eq t).trans hd).ge

theorem IsMorphism.image_boundary_of_isAtomIn_of_add_one_eq (hf : IsMorphism f)
    {U : LowerSet P} {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V)
    (hUV : f '' (U : Set P) ⊆ V) (hd : krullDim U = krullDim V) {k : ℕ}
    (hk : ((k + 1 : ℕ) : WithBot ℕ∞) = krullDim U) (α : Bool) :
    f '' P.boundary U k α = Q.boundary V k α := by
  obtain ⟨t, rfl⟩ := hU.exists_eq_Iic
  obtain ⟨s, rfl⟩ := hV.exists_eq_Iic
  have htd : grade ℕ t = k + 1 := by
    rw [LowerSet.krullDim_Iic] at hk
    exact_mod_cast hk.symm
  obtain rfl : f t = s := hf.apply_eq_of_image_Iic_subset hUV (by
    rw [LowerSet.krullDim_Iic, LowerSet.krullDim_Iic] at hd; exact_mod_cast hd)
  have := hf.image_boundary_Iic (x := t) (by omega) α
  rwa [hf.grade_eq, htd, Nat.add_sub_cancel] at this

theorem IsMorphism.eq_of_apply_eq_of_mem_boundaryFull_of_add_one_eq (hf : IsMorphism f)
    {U : LowerSet P} (hU : P.IsAtomIn U) {k : ℕ}
    (hk : ((k + 1 : ℕ) : WithBot ℕ∞) = krullDim U)
    {x y : P} (hx : x ∈ P.boundaryFull U k) (hy : y ∈ P.boundaryFull U k)
    (hxd : grade ℕ x = k) (hyd : grade ℕ y = k) (h : f x = f y) : x = y := by
  obtain ⟨t, rfl⟩ := hU.exists_eq_Iic
  have htd : grade ℕ t = k + 1 := by
    rw [LowerSet.krullDim_Iic] at hk
    exact_mod_cast hk.symm
  have hsub : P.boundaryFull (.Iic t) k ≤ .Iic t :=
    sup_le (boundary_le _ k false) (boundary_le _ k true)
  have hcov : ∀ z ∈ P.boundaryFull (.Iic t) k, grade ℕ z = k → z ⋖ t := fun z hz hzd =>
    GradeOrder.covBy_of_le_of_grade_eq_add_one (hsub hz) (by omega)
  exact hf.eq_of_covBy_of_apply_eq (hcov x hx hxd) (hcov y hy hyd) h

theorem IsMorphism.eq_of_apply_eq_of_grade_add_one_eq_of_image_boundary (hf : IsMorphism f)
    {U : LowerSet P} {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V)
    (hd : krullDim U = krullDim V) {k : ℕ} (hk : (k : WithBot ℕ∞) < krullDim U)
    (ha : ∀ x ∈ P.boundaryFull U k, ∀ y ∈ P.boundaryFull U k, grade ℕ x = k → grade ℕ y = k →
      f x = f y → x = y)
    (hc : ∀ α, f '' P.boundary U k α = Q.boundary V k α)
    {x y : P} (hx : x ∈ P.boundaryFull U k) (hy : y ∈ P.boundaryFull U k)
    (hxd : grade ℕ x + 1 = k) (hyd : grade ℕ y + 1 = k) (h : f x = f y) : x = y := by
  have hcF : f '' P.boundaryFull U k = Q.boundaryFull V k := by
    rw [boundaryFull, boundaryFull, LowerSet.coe_sup, LowerSet.coe_sup, Set.image_union, hc, hc]
  have hkV : (k : WithBot ℕ∞) < krullDim V := hd ▸ hk
  obtain ⟨x₁, x₂, hne, hX⟩ := exists_pair_covBy_of_mem_boundaryFull_of_isAtomIn hU hk hx hxd
  obtain ⟨x₁', x₂', -, hX'⟩ := exists_pair_covBy_of_mem_boundaryFull_of_isAtomIn hU hk hy hyd
  have hx₁ : x₁ ∈ P.boundaryFull U k ∧ x ⋖ x₁ := (hX x₁).2 (Or.inl rfl)
  have hx₂ : x₂ ∈ P.boundaryFull U k ∧ x ⋖ x₂ := (hX x₂).2 (Or.inr rfl)
  have hx₁' : x₁' ∈ P.boundaryFull U k ∧ y ⋖ x₁' := (hX' x₁').2 (Or.inl rfl)
  have hfx : f x ∈ Q.boundaryFull V k := (Set.ext_iff.1 hcF _).1 (mem_image_of_mem f hx)
  have hfxd : grade ℕ (f x) + 1 = k := by rw [hf.grade_eq]; exact hxd
  obtain ⟨y₁, y₂, -, hY⟩ := exists_pair_covBy_of_mem_boundaryFull_of_isAtomIn hV hkV hfx hfxd
  have himg : ∀ w z, z ∈ P.boundaryFull U k → w ⋖ z → f w = f x →
      f z = y₁ ∨ f z = y₂ := fun w z hz hwz hw => by
    refine (hY (f z)).1 ⟨(Set.ext_iff.1 hcF _).1 (mem_image_of_mem f hz), ?_⟩
    exact covBy_iff_lt_covBy_grade.2
      ⟨by rw [← hw]; exact hf.apply_lt_apply hwz.lt,
        by rw [← hw, hf.grade_eq, hf.grade_eq]; exact hwz.grade ℕ⟩
  have d₁ : grade ℕ x₁ = k := by have := Nat.covBy_iff_add_one_eq.1 (hx₁.2.grade ℕ); omega
  have d₂ : grade ℕ x₂ = k := by have := Nat.covBy_iff_add_one_eq.1 (hx₂.2.grade ℕ); omega
  have d₁' : grade ℕ x₁' = k := by have := Nat.covBy_iff_add_one_eq.1 (hx₁'.2.grade ℕ); omega
  have hne' : f x₁ ≠ f x₂ := fun e => hne (ha _ hx₁.1 _ hx₂.1 d₁ d₂ e)
  have h1 := himg x x₁ hx₁.1 hx₁.2 rfl
  have h2 := himg x x₂ hx₂.1 hx₂.2 rfl
  have h3 := himg y x₁' hx₁'.1 hx₁'.2 h.symm
  have key : x₁' = x₁ ∨ x₁' = x₂ := by
    rcases h3 with h3 | h3 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      first
        | exact Or.inl (ha _ hx₁'.1 _ hx₁.1 d₁' d₁ (h3.trans h1.symm))
        | exact Or.inr (ha _ hx₁'.1 _ hx₂.1 d₁' d₂ (h3.trans h2.symm))
        | exact absurd (h1.trans h2.symm) hne'
  exact hf.eq_of_covBy_of_apply_eq (key.elim (· ▸ hx₁.2) (· ▸ hx₂.2)) hx₁'.2 h

theorem IsMorphism.image_boundary_sub_one_of_image_boundary (hf : IsMorphism f)
    {U : LowerSet P} {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V)
    (hd : krullDim U = krullDim V) {k : ℕ} (hk : (k : WithBot ℕ∞) < krullDim U)
    (hb : ∀ x ∈ P.boundaryFull U k, ∀ y ∈ P.boundaryFull U k, grade ℕ x + 1 = k →
      grade ℕ y + 1 = k → f x = f y → x = y)
    (hc : ∀ α, f '' P.boundary U k α = Q.boundary V k α) (α : Bool) :
    f '' P.boundary U (k - 1) α = Q.boundary V (k - 1) α := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact hc α
  have hUm := hU.isMoleculeIn
  have hVm := hV.isMoleculeIn
  have hkV : (k : WithBot ℕ∞) < krullDim V := hd ▸ hk
  have hAr := hU.isRound.boundary k false
  have hBr := hV.isRound.boundary k false
  have hAd := hUm.krullDim_boundary hk.le false
  have hBd := hVm.krullDim_boundary hkV.le false
  have hcA := hc false
  rw [← hUm.isGlobular (k - 1) k (by omega) α false,
    ← hVm.isGlobular (k - 1) k (by omega) α false,
    boundary_eq_lowerClosure_facesIn_of_isRound hAr hAd (by omega),
    boundary_eq_lowerClosure_facesIn_of_isRound hBr hBd (by omega),
    hf.fibration.image_lowerClosure hf.monotone]
  congr 2
  ext w
  constructor
  · rintro ⟨z, ⟨hzA, hzd, hzc⟩, rfl⟩
    refine ⟨by rw [← hcA]; exact mem_image_of_mem f hzA, by rw [hf.grade_eq]; exact hzd,
      Set.disjoint_left.2 fun w' ⟨hcov, hor⟩ hw' => ?_⟩
    rw [← hcA] at hw'
    obtain ⟨y, hyA, rfl⟩ := hw'
    obtain ⟨z'', hz''y, hz''⟩ := hf.fibration hcov.le
    have hz''A : z'' ∈ P.boundary U k false := (P.boundary U k false).lower hz''y hyA
    have hdy : grade ℕ y = grade ℕ z + 1 := by
      have := (Nat.covBy_iff_add_one_eq.1 (hcov.grade ℕ)).symm
      rwa [hf.grade_eq, hf.grade_eq] at this
    have hdz'' : grade ℕ z'' = grade ℕ z := by rw [← hf.grade_eq, hz'', hf.grade_eq]
    have e : z'' = z := hb _ (boundary_le_boundaryFull U k false hz''A) _
      (boundary_le_boundaryFull U k false hzA) (by omega) (by omega) hz''
    subst e
    have hzy : z'' ⋖ y := GradeOrder.covBy_of_le_of_grade_eq_add_one hz''y hdy
    have ho : Q.orient hcov = P.orient hzy := by rw [← hf.orient_apply hzy]
    exact Set.disjoint_left.1 hzc ⟨hzy, ho.symm.trans hor⟩ hyA
  · rintro ⟨hwB, hwd, hwc⟩
    rw [← hcA] at hwB
    obtain ⟨z, hzA, rfl⟩ := hwB
    refine ⟨z, ⟨hzA, by rw [← hf.grade_eq]; exact hwd,
      Set.disjoint_left.2 fun y ⟨hzy, hor⟩ hyA => ?_⟩, rfl⟩
    exact Set.disjoint_left.1 hwc ⟨hf.covBy_apply hzy, (hf.orient_apply hzy).trans hor⟩
      (by rw [← hcA]; exact mem_image_of_mem f hyA)

theorem IsMorphism.injOn_and_image_boundary_of_isAtomIn (hf : IsMorphism f)
    {U : LowerSet P} {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V)
    (hUV : f '' (U : Set P) ⊆ V) (hd : krullDim U = krullDim V) (m : ℕ) :
    ∀ k : ℕ, ((k + m + 1 : ℕ) : WithBot ℕ∞) = krullDim U →
      (∀ x ∈ P.boundaryFull U k, ∀ y ∈ P.boundaryFull U k, grade ℕ x = k → grade ℕ y = k →
        f x = f y → x = y) ∧
      (∀ x ∈ P.boundaryFull U k, ∀ y ∈ P.boundaryFull U k, grade ℕ x + 1 = k →
        grade ℕ y + 1 = k → f x = f y → x = y) ∧
      (∀ α, f '' P.boundary U k α = Q.boundary V k α) := by
  induction m with
  | zero =>
    intro k hk
    have hk' : ((k + 1 : ℕ) : WithBot ℕ∞) = krullDim U := by simpa using hk
    have hkl : (k : WithBot ℕ∞) < krullDim U := by rw [← hk']; exact_mod_cast Nat.lt_succ_self k
    have ha : ∀ x ∈ P.boundaryFull U k, ∀ y ∈ P.boundaryFull U k, grade ℕ x = k →
        grade ℕ y = k → f x = f y → x = y := fun x hx y hy hxd hyd h =>
      hf.eq_of_apply_eq_of_mem_boundaryFull_of_add_one_eq hU hk' hx hy hxd hyd h
    have hc : ∀ α, f '' P.boundary U k α = Q.boundary V k α :=
      hf.image_boundary_of_isAtomIn_of_add_one_eq hU hV hUV hd hk'
    exact ⟨ha, fun x hx y hy hxd hyd h =>
      hf.eq_of_apply_eq_of_grade_add_one_eq_of_image_boundary hU hV hd hkl ha hc hx hy
        hxd hyd h, hc⟩
  | succ m ih =>
    intro k hk
    obtain ⟨-, hb', hc'⟩ := ih (k + 1) (by rw [← hk]; exact_mod_cast (by omega))
    have hkl : (k : WithBot ℕ∞) < krullDim U := by rw [← hk]; exact_mod_cast (by omega)
    have hkl' : ((k + 1 : ℕ) : WithBot ℕ∞) < krullDim U := by rw [← hk]; exact_mod_cast (by omega)
    have hsub := boundaryFull_le_boundaryFull_succ hU.isMoleculeIn.isGlobular k
    have ha : ∀ x ∈ P.boundaryFull U k, ∀ y ∈ P.boundaryFull U k, grade ℕ x = k →
        grade ℕ y = k → f x = f y → x = y := fun x hx y hy hxd hyd h =>
      hb' x (hsub hx) y (hsub hy) (by omega) (by omega) h
    have hc : ∀ α, f '' P.boundary U k α = Q.boundary V k α := fun α => by
      have := hf.image_boundary_sub_one_of_image_boundary hU hV hd hkl' hb' hc' α
      rwa [Nat.add_sub_cancel] at this
    exact ⟨ha, fun x hx y hy hxd hyd h =>
      hf.eq_of_apply_eq_of_grade_add_one_eq_of_image_boundary hU hV hd hkl ha hc hx hy
        hxd hyd h, hc⟩

theorem IsMorphism.image_boundary_of_isAtomIn (hf : IsMorphism f) {U : LowerSet P}
    {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V) (hUV : f '' (U : Set P) ⊆ V)
    (hd : krullDim U = krullDim V) {k : ℕ} (hk : (k : WithBot ℕ∞) < krullDim U) (α : Bool) :
    f '' P.boundary U k α = Q.boundary V k α := by
  obtain ⟨d, hdU⟩ := hU.isMoleculeIn.exists_krullDim_eq
  have hkd : k < d := by rw [hdU] at hk; exact_mod_cast hk
  exact (hf.injOn_and_image_boundary_of_isAtomIn hU hV hUV hd (d - k - 1) k
    (by rw [hdU]; exact_mod_cast (by omega))).2.2 α

theorem IsMorphism.eq_of_apply_eq_of_mem_boundaryFull_of_grade_eq (hf : IsMorphism f)
    {U : LowerSet P} {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V)
    (hUV : f '' (U : Set P) ⊆ V) (hd : krullDim U = krullDim V) {k : ℕ}
    (hk : (k : WithBot ℕ∞) < krullDim U)
    {x y : P} (hx : x ∈ P.boundaryFull U k) (hy : y ∈ P.boundaryFull U k)
    (hxd : grade ℕ x = k) (hyd : grade ℕ y = k) (h : f x = f y) : x = y := by
  obtain ⟨d, hdU⟩ := hU.isMoleculeIn.exists_krullDim_eq
  have hkd : k < d := by rw [hdU] at hk; exact_mod_cast hk
  exact (hf.injOn_and_image_boundary_of_isAtomIn hU hV hUV hd (d - k - 1) k
    (by rw [hdU]; exact_mod_cast (by omega))).1 x hx y hy hxd hyd h

theorem IsMorphism.eq_of_apply_eq_of_mem_boundaryFull_of_grade_add_one_eq (hf : IsMorphism f)
    {U : LowerSet P} {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V)
    (hUV : f '' (U : Set P) ⊆ V) (hd : krullDim U = krullDim V) {k : ℕ}
    (hk : (k : WithBot ℕ∞) < krullDim U)
    {x y : P} (hx : x ∈ P.boundaryFull U k) (hy : y ∈ P.boundaryFull U k)
    (hxd : grade ℕ x + 1 = k) (hyd : grade ℕ y + 1 = k) (h : f x = f y) : x = y := by
  obtain ⟨d, hdU⟩ := hU.isMoleculeIn.exists_krullDim_eq
  have hkd : k < d := by rw [hdU] at hk; exact_mod_cast hk
  exact (hf.injOn_and_image_boundary_of_isAtomIn hU hV hUV hd (d - k - 1) k
    (by rw [hdU]; exact_mod_cast (by omega))).2.1 x hx y hy hxd hyd h

theorem mem_bdryFull_of_isAtomIn_of_dim_lt {U : LowerSet P} (hU : P.IsAtomIn U)
    {x : P} (hx : x ∈ U) (hxd : (grade ℕ x : WithBot ℕ∞) < krullDim U) : x ∈ P.bdryFull U := by
  obtain ⟨t, rfl⟩ := hU.exists_eq_Iic
  rw [LowerSet.krullDim_Iic] at hxd
  rw [bdryFull, ← SetLike.mem_coe, coe_bdry_Iic_sup]
  exact lt_of_le_of_ne hx fun e => by subst e; exact lt_irrefl _ hxd

theorem IsMorphism.apply_mem_interior_boundary_of_isAtomIn (hf : IsMorphism f)
    {U : LowerSet P} {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V)
    (hUV : f '' (U : Set P) ⊆ V) (hd : krullDim U = krullDim V) {k : ℕ}
    (hk : (k : WithBot ℕ∞) < krullDim U)
    {α : Bool} {x : P} (hx : x ∈ P.interior (P.boundary U k α)) :
    f x ∈ Q.interior (Q.boundary V k α) :=
  hf.image_interior_subset (hU.isMoleculeIn.boundary k α) (hV.isMoleculeIn.boundary k α)
    (hf.image_boundary_of_isAtomIn hU hV hUV hd hk α).subset
    (by rw [hU.isMoleculeIn.krullDim_boundary hk.le,
      hV.isMoleculeIn.krullDim_boundary (hd ▸ hk).le])
    (mem_image_of_mem f hx)

theorem IsMorphism.apply_mem_interior_boundary_Iic (hf : IsMorphism f)
    {y : P} (hy : P.IsAtomIn (.Iic y)) (hfy : Q.IsAtomIn (.Iic (f y)))
    (hpos : 0 < grade ℕ y) {β : Bool} {x : P}
    (hx : x ∈ P.interior (P.boundary (.Iic y) (grade ℕ y - 1) β)) :
    f x ∈ Q.interior (Q.boundary (.Iic (f y)) (grade ℕ y - 1) β) := by
  have himg := hf.image_boundary_Iic hpos β
  rw [hf.grade_eq] at himg
  have hle : ((grade ℕ y - 1 : ℕ) : WithBot ℕ∞) ≤ krullDim (LowerSet.Iic y) := by
    rw [LowerSet.krullDim_Iic]; exact_mod_cast (by omega)
  have hle' : ((grade ℕ y - 1 : ℕ) : WithBot ℕ∞) ≤ krullDim (LowerSet.Iic (f y)) := by
    rw [LowerSet.krullDim_Iic, hf.grade_eq]; exact_mod_cast (by omega)
  exact hf.image_interior_subset (hy.isMoleculeIn.boundary _ β)
    (hfy.isMoleculeIn.boundary _ β) himg.subset
    (by rw [hy.isMoleculeIn.krullDim_boundary hle, hfy.isMoleculeIn.krullDim_boundary hle'])
    (mem_image_of_mem f hx)

theorem IsMorphism.eq_of_apply_eq_of_mem_interior_boundary_of_isAtomIn (hf : IsMorphism f)
    (ℓ : ℕ) : ∀ {U : LowerSet P} {V : LowerSet Q}, P.IsAtomIn U → Q.IsAtomIn V →
      f '' (U : Set P) ⊆ V → krullDim U = krullDim V →
      ∀ {k : ℕ}, (k : WithBot ℕ∞) < krullDim U → ∀ {α : Bool}
      {x x' : P}, x ∈ P.interior (P.boundary U k α) →
      x' ∈ P.interior (P.boundary U k α) → f x = f x' → grade ℕ x + ℓ = k → x = x' := by
  induction ℓ with
  | zero =>
    intro U V hU hV hUV hd k hk α x x' hx hx' h hxd
    have hxd' : grade ℕ x' = k := by rw [← hf.grade_eq, ← h, hf.grade_eq]; omega
    exact hf.eq_of_apply_eq_of_mem_boundaryFull_of_grade_eq hU hV hUV hd hk
      (boundary_le_boundaryFull _ _ _ (P.interior_subset _ hx))
      (boundary_le_boundaryFull _ _ _ (P.interior_subset _ hx')) (by omega) hxd' h
  | succ ℓ ih =>
    intro U V hU hV hUV hd k hk α x x' hx hx' h hxd
    have hxd' : grade ℕ x' = grade ℕ x := by rw [← hf.grade_eq, ← h, hf.grade_eq]
    have hkV : (k : WithBot ℕ∞) < krullDim V := hd ▸ hk
    have hB := hU.isMoleculeIn.boundary k α
    have hBd := hU.isMoleculeIn.krullDim_boundary hk.le α
    have hC := hV.isMoleculeIn.boundary k α
    have hCd := hV.isMoleculeIn.krullDim_boundary hkV.le α
    have himg := hf.image_boundary_of_isAtomIn hU hV hUV hd hk α
    have htop : ∀ z, z ∈ P.interior (P.boundary U k α) → grade ℕ z < k →
        ∃ y ∈ P.boundary U k α, grade ℕ y = k ∧
          z ∈ P.interior (P.boundary (.Iic y) (k - 1) true) := by
      intro z hz hzd
      rcases (mem_interior_iff_of_isMoleculeIn hB (P.interior_subset _ hz)).1 hz with
        h0 | ⟨-, yp, hyp, -, -, hpd, -, hp, -⟩
      · have : grade ℕ z = k := by exact_mod_cast h0.trans hBd
        omega
      · have hpd' : grade ℕ yp = k := by exact_mod_cast hpd.trans hBd
        rw [hpd'] at hp
        exact ⟨yp, hyp, hpd', hp⟩
    obtain ⟨y, hy, hyd, hxy⟩ := htop x hx (by omega)
    obtain ⟨y', hy', hy'd, hxy'⟩ := htop x' hx' (by omega)
    have hfmem : ∀ w ∈ P.boundary U k α, f w ∈ Q.boundary V k α := fun w hw =>
      (Set.ext_iff.1 himg _).1 (mem_image_of_mem f hw)
    have hA : ∀ w ∈ P.boundary U k α, P.IsAtomIn (.Iic w) := fun w hw =>
      hB.isAtomIn_Iic hw
    have hfA : ∀ w ∈ P.boundary U k α, Q.IsAtomIn (.Iic (f w)) := fun w hw =>
      hC.isAtomIn_Iic (hfmem w hw)
    have hfx : ∀ {w z : P}, w ∈ P.boundary U k α → grade ℕ w = k →
        z ∈ P.interior (P.boundary (.Iic w) (k - 1) true) →
        f z ∈ Q.interior (Q.boundary (.Iic (f w)) (grade ℕ (f w) - 1) true) :=
      fun {w z} hw hwd hz => by
        have := hf.apply_mem_interior_boundary_Iic (hA w hw) (hfA w hw)
          (by omega) (hwd.symm ▸ hz)
        rwa [hf.grade_eq]
    have hfyd : ∀ w, grade ℕ w = k →
        (grade ℕ (f w) : WithBot ℕ∞) = krullDim (Q.boundary V k α) := fun w hw => by
      rw [hf.grade_eq, hCd, hw]
    have e : f y = f y' := eq_of_mem_interior_boundary_Iic hC (hfmem y hy)
      (hfmem y' hy') (hfyd y hyd) (hfyd y' hy'd) true (hfx hy hyd hxy)
      (h ▸ hfx hy' hy'd hxy')
    obtain rfl : y = y' := hf.eq_of_apply_eq_of_mem_boundaryFull_of_grade_eq hU hV hUV hd hk
      (boundary_le_boundaryFull _ _ _ hy) (boundary_le_boundaryFull _ _ _ hy') hyd hy'd e
    exact ih (hA y hy) (hfA y hy) (hf.image_Iic y).subset
      (by rw [LowerSet.krullDim_Iic, LowerSet.krullDim_Iic, hf.grade_eq])
      (by rw [LowerSet.krullDim_Iic]; exact_mod_cast (by omega : k - 1 < grade ℕ y))
      hxy hxy' h (by omega)

theorem IsMorphism.eq_of_apply_eq_of_isAtomIn (hf : IsMorphism f) {U : LowerSet P}
    {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V) (hUV : f '' (U : Set P) ⊆ V)
    (hd : krullDim U = krullDim V) {x y : P} (hx : x ∈ U) (hy : y ∈ U) (h : f x = f y) :
    x = y := by
  have hyd : grade ℕ y = grade ℕ x := by rw [← hf.grade_eq, ← h, hf.grade_eq]
  rcases (grade_le_krullDim (⟨x, hx⟩ : U)).eq_or_lt with hxd | hxd
  · obtain ⟨t, rfl⟩ := hU.exists_eq_Iic
    rw [LowerSet.krullDim_Iic] at hxd
    have hxt : grade ℕ x = grade ℕ t := by exact_mod_cast hxd
    rw [GradeOrder.eq_of_le_of_grade_le hx (by omega),
      GradeOrder.eq_of_le_of_grade_le hy (by omega)]
  · have hni : ∀ z ∈ U, (grade ℕ z : WithBot ℕ∞) < krullDim U → z ∉ P.interior U :=
      fun z hz hzd hi =>
        hi.2 (hU.isMoleculeIn.properBoundary_eq_bdryFull ▸
          mem_bdryFull_of_isAtomIn_of_dim_lt hU hz hzd)
    rcases hU.isMoleculeIn.isGlobular.mem_interior_or_exists_mem_interior_boundary hx with
      hi | ⟨k, hk, α, hxk⟩
    · exact absurd hi (hni x hx hxd)
    rcases hU.isMoleculeIn.isGlobular.mem_interior_or_exists_mem_interior_boundary hy with
      hi | ⟨j, hj, β, hyj⟩
    · exact absurd hi (hni y hy (hyd.symm ▸ hxd))
    have hfx := hf.apply_mem_interior_boundary_of_isAtomIn hU hV hUV hd hk hxk
    have hfy := hf.apply_mem_interior_boundary_of_isAtomIn hU hV hUV hd hj hyj
    rw [← h] at hfy
    obtain ⟨rfl, rfl⟩ := hV.isRound.eq_of_mem_interior_boundary hV.isMoleculeIn (hd ▸ hk)
      (hd ▸ hj) hfx hfy
    have hxk' := grade_le_of_mem_boundary (P.interior_subset _ hxk)
    exact hf.eq_of_apply_eq_of_mem_interior_boundary_of_isAtomIn (k - grade ℕ x) hU hV hUV hd hk
      hxk hyj h (by omega)

theorem IsMorphism.image_eq_of_isAtomIn (hf : IsMorphism f) {U : LowerSet P}
    {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V) (hUV : f '' (U : Set P) ⊆ V)
    (hd : krullDim U = krullDim V) : f '' (U : Set P) = V := by
  obtain ⟨t, rfl⟩ := hU.exists_eq_Iic
  obtain ⟨s, rfl⟩ := hV.exists_eq_Iic
  have hts : grade ℕ t = grade ℕ s := by
    rw [LowerSet.krullDim_Iic, LowerSet.krullDim_Iic] at hd
    exact_mod_cast hd
  have e : f t = s := hf.apply_eq_of_image_Iic_subset hUV hts
  rw [hf.image_Iic, e]

theorem IsMorphism.eq_of_apply_eq_of_isAtomIn_of_isRDC (hf : IsMorphism f) (hQ : IsRDC Q)
    {U : LowerSet P} (hU : P.IsAtomIn U) {x y : P} (hx : x ∈ U) (hy : y ∈ U)
    (h : f x = f y) : x = y := by
  obtain ⟨t, rfl⟩ := hU.exists_eq_Iic
  refine hf.eq_of_apply_eq_of_isAtomIn hU ⟨hQ (f t), f t, rfl⟩ ?_ ?_ hx hy h
  · rw [hf.image_Iic]
  · rw [LowerSet.krullDim_Iic, LowerSet.krullDim_Iic, hf.grade_eq]

theorem IsMorphism.isLocalEmbedding_of_isRDC (hf : IsMorphism f) (hP : IsRDC P)
    (hQ : IsRDC Q) : IsLocalEmbedding f := fun x =>
  .of_continuous_injective_isClosedMap (hf.continuous.comp continuous_subtype_val)
    (fun y z h => Subtype.ext (hf.eq_of_apply_eq_of_isAtomIn_of_isRDC hQ ⟨hP x, x, rfl⟩
      ((Set.ext_iff.1 IsUpperSet.closure_singleton _).1 y.2)
      ((Set.ext_iff.1 IsUpperSet.closure_singleton _).1 z.2) h))
    (hf.isClosedMap.comp isClosed_closure.isClosedEmbedding_subtypeVal.isClosedMap)

end Atoms.Molecule.OGP
