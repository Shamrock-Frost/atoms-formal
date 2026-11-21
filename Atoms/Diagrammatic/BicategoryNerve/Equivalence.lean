import Atoms.Diagrammatic.BicategoryNerve.Biequivalence

open CategoryTheory Atoms.Shape Atoms.Diagrammatic.PastingDiagram
open CategoryTheory.Bicategory (PathCell pathComp pathCompCompIso whiskerLeftIso
  whiskerRightIso)
open scoped CategoryTheory.Bicategory

universe w v u

namespace Atoms.Diagrammatic

variable {B : Type u} [Bicategory.{w, v} B]

private theorem nerveComposite_boundary_zero_of_eq
    {d : PastingDiagram (bicategoryNerve.{w, v, u} B)} (hd : d.dim ≤ 2) {a b : B}
    {P Q : Quiver.Path a b} {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q}
    (hP : d.nerveComposite hd = ⟨a, b, P, Q, φ⟩) (α : Bool) (hb : (d.boundary 0 α).dim ≤ 2) :
    (d.boundary 0 α).nerveComposite hb = ⟨cond α b a, cond α b a, .nil, .nil, 𝟙 _⟩ := by
  rw [nerveComposite_boundary_zero d hd α hb, hP]

private theorem nerveComposite_paste_zero_of_id
    {u v : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    (hp : u.Pastable v 0) (hu : u.dim ≤ 2) (hv : v.dim ≤ 2) (hw : (u.paste v 0 hp).dim ≤ 2)
    {a c b : B} {P : Quiver.Path a c} {Q : Quiver.Path c b}
    (hP : u.nerveComposite hu = ⟨a, c, P, P, 𝟙 _⟩)
    (hQ : v.nerveComposite hv = ⟨c, b, Q, Q, 𝟙 _⟩) :
    (u.paste v 0 hp).nerveComposite hw = ⟨a, b, P.comp Q, P.comp Q, 𝟙 _⟩ := by
  refine (nerveComposite_pasteAlong_zero u v hp.1.iso hp.1.map_comm hu hv hw hP hQ).trans ?_
  simp

theorem Parallel.equivalent_of_pathComp_iso
    {s t : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)} (h : Parallel s t) (hs : s.dim = 1)
    (hsd : s.dim ≤ 2) (htd : t.dim ≤ 2) {a b : B} {P Q : Quiver.Path a b}
    (hs' : s.nerveComposite hsd = ⟨a, b, P, P, 𝟙 _⟩)
    (ht' : t.nerveComposite htd = ⟨a, b, Q, Q, 𝟙 _⟩)
    (θ : pathComp (𝟭q B) P ≅ pathComp (𝟭q B) Q) : Equivalent s t := by
  obtain ⟨z, hz, hzc⟩ := h.exists_nerveFiller_one hs hsd htd hs' ht' θ.hom
  exact Equivalent.of_hasRoundType hz (bicategoryNerve_mem_equivalences_of_isIso _
    (hz.dim_eq.trans (by rw [hs])) (hzc _))

theorem bicategoryNerve_mem_equivalences_of_equivalence
    (e : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)) (he : e.dim = 1) {a b : B}
    {P : Quiver.Path a b} (hP : e.nerveComposite (he.trans_le one_le_two) = ⟨a, b, P, P, 𝟙 _⟩)
    (E : a ≌ b) (hE : E.hom = pathComp (𝟭q B) P) :
    e ∈ equivalences (bicategoryNerve.{w, v, u} B) := by
  revert hE
  obtain ⟨f, g, η, ε, -⟩ := E
  rintro rfl
  have hb (α : Bool) : (e.boundary 0 α).dim = 0 := dim_boundary _ (Nat.zero_le _) α
  have hb₂ (α : Bool) : (e.boundary 0 α).dim ≤ 2 := (hb α).trans_le (Nat.zero_le 2)
  have hc := nerveComposite_boundary_zero_of_eq (he.trans_le one_le_two) hP
  let a' : RoundPastingDiagram (bicategoryNerve.{w, v, u} B) :=
    ⟨e.boundary 0 false, isRound_boundary_of_isRound e.isRound 0 false⟩
  let b' : RoundPastingDiagram (bicategoryNerve.{w, v, u} B) :=
    ⟨e.boundary 0 true, isRound_boundary_of_isRound e.isRound 0 true⟩
  obtain ⟨x, hx, hxc⟩ := (show Parallel b' a' from ⟨(hb true).trans (hb false).symm,
    .inl (hb true)⟩).exists_nerveFiller_zero (hb true) (hb₂ true) (hb₂ false)
      (hc true _) (hc false _) g
  have he₁ : HasBdry false 0 e.toPastingDiagram a'.toPastingDiagram b'.toPastingDiagram :=
    ⟨he, hb false, hb true, .refl _, .refl _⟩
  have he₂ : HasBdry false 0 (PastingDiagram.ofCell x) b'.toPastingDiagram a'.toPastingDiagram :=
    .of_dim_eq (hb true) hx.dim_eq (hb true) (hb false) hx.source hx.target
  have hte : HasRoundType e.toPastingDiagram a' b' :=
    .of_equiv_boundary (hb false) (hb true) he fun β => by cases β <;> exact .refl _
  have hed : e.dim ≤ 2 := he.trans_le one_le_two
  have hxd : (PastingDiagram.ofCell x).dim ≤ 2 := he₂.dim_h.trans_le one_le_two
  have hp := he₁.pastable he₂ (.refl _)
  have hq := he₂.pastable he₁ (.refl _)
  have hpd : (e.paste (PastingDiagram.ofCell x) 0 hp).dim = 1 := by
    rw [dim_paste, he, he₂.dim_h]; rfl
  have hqd : ((PastingDiagram.ofCell x).paste e.toPastingDiagram 0 hq).dim = 1 := by
    rw [dim_paste, he, he₂.dim_h]; rfl
  have hud (α : Bool) : (e.boundary 0 α).unit.dim ≤ 2 := by
    rw [dim_unit, hb α]; omega
  refine mem_equivalences_of_equivalent_unit (e' := cellRound x) he₁ he₂ a'.isRound b'.isRound
    ?_ ?_
  · refine Parallel.equivalent_of_pathComp_iso (HasRoundType.parallel
      (c := ⟨_, isRound_paste_of_dim e (cellRound x) he₁.dim_h he₂.dim_h hp⟩)
      (d := a'.isRound.unit) (hte.paste hx (.refl _) (hb false) hp) (hasRoundType_unit a'))
      hpd (hpd.trans_le one_le_two) (hud false)
      (nerveComposite_paste_zero_of_id hp hed hxd (hpd.trans_le one_le_two) hP (hxc hxd))
      (nerveComposite_unit_of_dim_eq_zero _ (hb false) (hud false) (hc false _))
      (pathCompCompIso (𝟭q B) P g.toPath ≪≫ whiskerLeftIso _ (λ_ g) ≪≫ η.symm ≪≫
        (λ_ _).symm)
  · refine Parallel.equivalent_of_pathComp_iso (HasRoundType.parallel (c := b'.isRound.unit)
      (d := ⟨_, isRound_paste_of_dim (cellRound x) e he₂.dim_h he₁.dim_h hq⟩)
      (hasRoundType_unit b') (hx.paste hte (.refl _) (hb true) hq))
      ((dim_unit _).trans (by rw [hb true])) (hud true) (hqd.trans_le one_le_two)
      (nerveComposite_unit_of_dim_eq_zero _ (hb true) (hud true) (hc true _))
      (nerveComposite_paste_zero_of_id hq hxd hed (hqd.trans_le one_le_two) (hxc hxd) hP)
      (λ_ _ ≪≫ ε.symm ≪≫ whiskerRightIso (λ_ g).symm _ ≪≫
        (pathCompCompIso (𝟭q B) g.toPath P).symm)

theorem exists_nerveComposite_eq_of_hasBdry {d x y : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    (ht : HasBdry false 0 d x y) (hd : d.dim ≤ 2) (hx : x.dim ≤ 2) (hy : y.dim ≤ 2) {a b : B}
    (hxc : x.nerveComposite hx = ⟨a, a, .nil, .nil, 𝟙 _⟩)
    (hyc : y.nerveComposite hy = ⟨b, b, .nil, .nil, 𝟙 _⟩) :
    ∃ P : Quiver.Path a b, d.nerveComposite hd = ⟨a, b, P, P, 𝟙 _⟩ := by
  have hb (α : Bool) : (d.boundary 0 α).dim ≤ 2 :=
    (dim_boundary _ (Nat.zero_le _) α).trans_le (Nat.zero_le 2)
  have key : ∀ C : PathCell B, C.src = a → C.tgt = b →
      (∃ p : Quiver.Path C.src C.tgt, C = ⟨_, _, p, p, 𝟙 _⟩) →
        ∃ P : Quiver.Path a b, C = ⟨a, b, P, P, 𝟙 _⟩ := by
    rintro ⟨s, t, R, S, φ⟩ rfl rfl ⟨p, hp⟩
    exact ⟨p, hp⟩
  exact key _
    (congrArg PathCell.src ((nerveComposite_boundary_zero d hd false (hb false)).symm.trans
      ((nerveComposite_congr ht.side (hb false) hx).trans hxc)))
    (congrArg PathCell.src ((nerveComposite_boundary_zero d hd true (hb true)).symm.trans
      ((nerveComposite_congr ht.other (hb true) hy).trans hyc)))
    (exists_nerveComposite_eq_of_dim_le_one d hd ht.dim_h.le)

theorem nonempty_pathComp_iso_of_hasBdry {z c d : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    (hz : z.IsRound)
    (hm : (⟨z, hz⟩ : RoundPastingDiagram _) ∈ equivalences (bicategoryNerve.{w, v, u} B))
    (ht : HasBdry false 1 z c d) (hcd : c.dim ≤ 2) (hdd : d.dim ≤ 2) {a b : B}
    {P Q : Quiver.Path a b} (hc : c.nerveComposite hcd = ⟨a, b, P, P, 𝟙 _⟩)
    (hd : d.nerveComposite hdd = ⟨a, b, Q, Q, 𝟙 _⟩) :
    Nonempty (pathComp (𝟭q B) P ≅ pathComp (𝟭q B) Q) := by
  have hz₂ : z.dim ≤ 2 := ht.dim_h.le
  have hb (α : Bool) : (z.boundary 1 α).dim ≤ 2 :=
    (dim_boundary _ (by rw [ht.dim_h]; omega) α).trans_le one_le_two
  have h₀ := (nerveComposite_boundary_one z hz₂ false (hb false)).symm.trans
    ((nerveComposite_congr ht.side (hb false) hcd).trans hc)
  have h₁ := (nerveComposite_boundary_one z hz₂ true (hb true)).symm.trans
    ((nerveComposite_congr ht.other (hb true) hdd).trans hd)
  rcases hφ : z.nerveComposite hz₂ with ⟨x, y, R, S, φ⟩
  have := isIso_of_bicategoryNerve_mem_equivalences ⟨z, hz⟩ ht.dim_h hφ hm
  rw [hφ] at h₀ h₁
  obtain ⟨rfl, rfl, hR, -, -⟩ := PathCell.mk.inj h₀
  obtain ⟨-, -, hS, -, -⟩ := PathCell.mk.inj h₁
  obtain rfl := eq_of_heq hR
  obtain rfl := eq_of_heq hS
  exact ⟨asIso φ⟩

theorem IsWeakInverse.exists_equivalence {e e' : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)}
    (h : IsWeakInverse e.toPastingDiagram e'.toPastingDiagram) (he : e.dim = 1) (he' : e'.dim = 1)
    {a b : B} {P : Quiver.Path a b} {Q : Quiver.Path b a}
    (hP : e.nerveComposite (he.trans_le one_le_two) = ⟨a, b, P, P, 𝟙 _⟩)
    (hQ : e'.nerveComposite (he'.trans_le one_le_two) = ⟨b, a, Q, Q, 𝟙 _⟩) :
    ∃ E : a ≌ b, E.hom = pathComp (𝟭q B) P ∧ E.inv = pathComp (𝟭q B) Q := by
  have hb (α : Bool) : (e.boundary 0 α).dim = 0 := dim_boundary _ (Nat.zero_le _) α
  have hud (α : Bool) : (e.boundary 0 α).unit.dim ≤ 2 := by
    rw [dim_unit, hb α]; omega
  have hc := nerveComposite_boundary_zero_of_eq (he.trans_le one_le_two) hP
  have ht : HasBdry false 0 e.toPastingDiagram (e.boundary 0 false) (e.boundary 0 true) :=
    ⟨he, hb false, hb true, .refl _, .refl _⟩
  obtain ⟨-, ht', ⟨z, hz, hzm, hzt⟩, ⟨k, hk, hkm, hkt⟩⟩ := h.spec ht
  have hp := ht.pastable ht' (.refl _)
  have hq := ht'.pastable ht (.refl _)
  rw [pasteOr_of hp] at hzt
  rw [pasteOr_of hq] at hkt
  have hpd : (e.paste e'.toPastingDiagram 0 hp).dim ≤ 2 := by
    rw [dim_paste, he, he']; omega
  have hqd : (e'.paste e.toPastingDiagram 0 hq).dim ≤ 2 := by
    rw [dim_paste, he, he']; omega
  obtain ⟨η⟩ := nonempty_pathComp_iso_of_hasBdry hz hzm hzt hpd (hud false)
    (nerveComposite_paste_zero_of_id hp (he.trans_le one_le_two) (he'.trans_le one_le_two) hpd hP
      hQ)
    (nerveComposite_unit_of_dim_eq_zero _ (hb false) (hud false) (hc false _))
  obtain ⟨ε⟩ := nonempty_pathComp_iso_of_hasBdry hk hkm hkt (hud true) hqd
    (nerveComposite_unit_of_dim_eq_zero _ (hb true) (hud true) (hc true _))
    (nerveComposite_paste_zero_of_id hq (he'.trans_le one_le_two) (he.trans_le one_le_two) hqd hQ
      hP)
  exact ⟨.mkOfAdjointifyCounit ((λ_ _).symm ≪≫ η.symm ≪≫ pathCompCompIso _ P Q)
    ((pathCompCompIso _ Q P).symm ≪≫ ε.symm ≪≫ λ_ _), rfl, rfl⟩

theorem bicategoryNerve_mem_equivalences_iff_of_dim_eq_one
    (e : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)) (he : e.dim = 1) {a b : B}
    {P : Quiver.Path a b} (hP : e.nerveComposite (he.trans_le one_le_two) = ⟨a, b, P, P, 𝟙 _⟩) :
    e ∈ equivalences (bicategoryNerve.{w, v, u} B) ↔
      ∃ E : a ≌ b, E.hom = pathComp (𝟭q B) P := by
  refine ⟨fun hm => ?_, fun ⟨E, hE⟩ => bicategoryNerve_mem_equivalences_of_equivalence e he hP E hE⟩
  obtain ⟨e', hw⟩ := exists_isWeakInverse hm
  have hb (α : Bool) : (e.boundary 0 α).dim = 0 := dim_boundary _ (Nat.zero_le _) α
  have hc := nerveComposite_boundary_zero_of_eq (he.trans_le one_le_two) hP
  obtain ⟨-, ht'⟩ := hw.hasBdry
    (⟨he, hb false, hb true, .refl _, .refl _⟩ :
      HasBdry false 0 e.toPastingDiagram (e.boundary 0 false) (e.boundary 0 true))
  have hb₂ (α : Bool) : (e.boundary 0 α).dim ≤ 2 := (hb α).trans_le (Nat.zero_le 2)
  obtain ⟨Q, hQ⟩ := exists_nerveComposite_eq_of_hasBdry ht' (ht'.dim_h.trans_le one_le_two)
    (hb₂ true) (hb₂ false) (hc true _) (hc false _)
  obtain ⟨E, hE, -⟩ := hw.exists_equivalence he ht'.dim_h hP hQ
  exact ⟨E, hE⟩

theorem exists_cell_nerveComposite_eq_toPath {a b : B} (f : a ⟶ b) :
    ∃ (U : Atom) (x : diagram (bicategoryNerve.{w, v, u} B) U),
      HasRoundType (PastingDiagram.ofCell x) (cellRound (nervePointCell.{w, v, u} a))
        (cellRound (nervePointCell.{w, v, u} b)) ∧
      ∀ hd, (PastingDiagram.ofCell x).nerveComposite hd = ⟨a, b, f.toPath, f.toPath, 𝟙 _⟩ :=
  ⟨_, (show Parallel (cellRound (nervePointCell.{w, v, u} a)) (cellRound (nervePointCell b)) from
    ⟨rfl, .inl dimension_atomPoint⟩).exists_nerveFiller_zero dimension_atomPoint
      (dimension_atomPoint.trans_le (Nat.zero_le 2)) (dimension_atomPoint.trans_le (Nat.zero_le 2))
      (nerveComposite_nervePointCell a _) (nerveComposite_nervePointCell b _) f⟩

theorem isInftyCategory_one_bicategoryNerve_iff :
    IsInftyCategory 1 (bicategoryNerve.{w, v, u} B) ↔
      ∀ {a b : B} {f g : a ⟶ b} (φ : f ⟶ g), IsIso φ := by
  refine ⟨fun hX a b f g φ => ?_, isInftyCategory_one_bicategoryNerve⟩
  obtain ⟨U, x, hx, hxc⟩ := exists_cell_nerveComposite_eq_toPath f
  obtain ⟨V, y, hy, hyc⟩ := exists_cell_nerveComposite_eq_toPath g
  have hd : (cellRound x).dim = 1 := hx.dim_eq.trans (congrArg (· + 1) dimension_atomPoint)
  have hpar : Parallel (cellRound x) (cellRound y) := HasRoundType.parallel hx hy
  obtain ⟨z, hz, hzc⟩ := hpar.exists_nerveFiller_one hd (hd.trans_le one_le_two)
    ((hy.dim_eq.trans (congrArg (· + 1) dimension_atomPoint)).trans_le one_le_two) (hxc _)
    (hyc _) ((λ_ f).hom ≫ φ ≫ (λ_ g).inv)
  have hz₂ : (cellRound z).dim = 2 := hz.dim_eq.trans (by rw [hd])
  have hU : (1 : ℕ∞) < hpar.cellShape.dimension := by
    have : hpar.cellShape.dimension = 2 := hz₂
    rw [this]
    exact_mod_cast one_lt_two
  have : IsIso ((λ_ f).hom ≫ φ ≫ (λ_ g).inv) :=
    isIso_of_bicategoryNerve_mem_equivalences (cellRound z) hz₂ (hzc _) (hX.2 _ z hU)
  have key : φ = (λ_ f).inv ≫ ((λ_ f).hom ≫ φ ≫ (λ_ g).inv) ≫ (λ_ g).hom := by simp
  rw [key]
  infer_instance

theorem isInftyCategory_zero_bicategoryNerve_iff :
    IsInftyCategory 0 (bicategoryNerve.{w, v, u} B) ↔
      (∀ {a b : B} {f g : a ⟶ b} (φ : f ⟶ g), IsIso φ) ∧
        ∀ {a b : B} (f : a ⟶ b), ∃ E : a ≌ b, E.hom = f := by
  refine ⟨fun hX => ⟨isInftyCategory_one_bicategoryNerve_iff.1
    ⟨hX.1, fun U x hU => hX.2 U x (zero_lt_one.trans hU)⟩, fun {a b} f => ?_⟩,
    fun ⟨h₂, h₁⟩ => ⟨hasWeakComposites_bicategoryNerve, fun U x hU => ?_⟩⟩
  · obtain ⟨U, x, hx, hxc⟩ := exists_cell_nerveComposite_eq_toPath f
    have hd : (cellRound x).dim = 1 := hx.dim_eq.trans (congrArg (· + 1) dimension_atomPoint)
    have hU : (0 : ℕ∞) < U.dimension := by
      have : U.dimension = 1 := hd
      rw [this]
      exact zero_lt_one
    obtain ⟨E, hE⟩ := (bicategoryNerve_mem_equivalences_iff_of_dim_eq_one (cellRound x) hd
      (hxc _)).1 (hX.2 U x hU)
    exact ⟨.mkOfAdjointifyCounit (E.unit ≪≫ whiskerRightIso (eqToIso hE ≪≫ λ_ f) _)
      (whiskerLeftIso _ (eqToIso hE ≪≫ λ_ f).symm ≪≫ E.counit), rfl⟩
  · have hU' : 0 < U.dimension := by exact_mod_cast hU
    rcases (show U.dimension = 1 ∨ 1 < U.dimension by omega) with h | h
    · have hd : (cellRound x).dim = 1 := h
      obtain ⟨P, hP⟩ := exists_nerveComposite_eq_of_dim_le_one (cellRound x).toPastingDiagram
        (hd.trans_le one_le_two) hd.le
      obtain ⟨E, hE⟩ := h₁ (pathComp (𝟭q B) P)
      exact bicategoryNerve_mem_equivalences_of_equivalence (cellRound x) hd hP E hE
    · exact (isInftyCategory_one_bicategoryNerve h₂).2 U x (by exact_mod_cast h)

end Atoms.Diagrammatic
