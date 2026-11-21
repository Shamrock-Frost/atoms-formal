import Atoms.Diagrammatic.Horn.Basic
import Atoms.Diagrammatic.Localization.WalkingEquivalence

open CategoryTheory Limits MorphismProperty Opposite Atoms.Shape Atoms.Molecule Atoms.Molecule.OGP
  Atoms.Diagrammatic.PastingDiagram

universe u
namespace Atoms.Diagrammatic

def sourceHorns : MorphismProperty DiagSet.{u} :=
  ofHoms fun p : {p : Σ U : Atom, U.ogp // ∃ _ : p.2 ⋖ p.1.top,
      p.1.ogp.boundary (LowerSet.Iic p.2) 0 false = p.1.ogp.boundary ⊤ 0 false} =>
    hornInclusion.{u} (atomicHornDataOfCovBy p.1.1 p.1.2 p.2.fst).toHornData

private theorem isPushout_sigma_map {J : Type u} {Z₁ Z₂ Z₃ Z₄ : J → DiagSet.{u}}
    {f : ∀ j, Z₁ j ⟶ Z₂ j} {g : ∀ j, Z₁ j ⟶ Z₃ j} {h : ∀ j, Z₂ j ⟶ Z₄ j}
    {k : ∀ j, Z₃ j ⟶ Z₄ j} (H : ∀ j, IsPushout (f j) (g j) (h j) (k j)) :
    IsPushout (Limits.Sigma.map f) (Limits.Sigma.map g) (Limits.Sigma.map h)
      (Limits.Sigma.map k) := by
  refine IsPushout.of_isColimit' ⟨Sigma.hom_ext _ _ fun j => by
    simp only [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_map, (H j).w_assoc]⟩
    (PushoutCocone.IsColimit.mk _
      (fun s => Sigma.desc fun j => (H j).desc (Sigma.ι _ j ≫ s.inl) (Sigma.ι _ j ≫ s.inr) (by
        simpa only [Limits.Sigma.ι_map_assoc] using Sigma.ι _ j ≫= s.condition))
      (fun s => Sigma.hom_ext _ _ fun j => by
        simp only [Limits.Sigma.ι_map_assoc, Sigma.ι_desc, IsPushout.inl_desc])
      (fun s => Sigma.hom_ext _ _ fun j => by
        simp only [Limits.Sigma.ι_map_assoc, Sigma.ι_desc, IsPushout.inr_desc])
      (fun s m hl hr => Sigma.hom_ext _ _ fun j => (H j).hom_ext
        (by simpa only [Sigma.ι_desc, IsPushout.inl_desc, Limits.Sigma.ι_map_assoc]
          using Sigma.ι _ j ≫= hl)
        (by simpa only [Sigma.ι_desc, IsPushout.inr_desc, Limits.Sigma.ι_map_assoc]
          using Sigma.ι _ j ≫= hr)))

section Lattice

variable (W : Atom) {k : ℕ} (α : Bool) {x : W.ogp} {K Uu : LowerSet W.ogp}

private theorem mem_sup_of_ne (hW : W.dimension = k + 2) (hx : grade ℕ x = k + 1)
    (hp : W.ogp.IsPastingIn k (cond α (LowerSet.Iic x) K) (cond α K (LowerSet.Iic x))
      (W.ogp.boundary ⊤ (k + 1) α))
    (hU : Uu = W.ogp.boundary ⊤ (k + 1) (!α)) {z : W.ogp} (hzt : z ≠ W.top) (hzx : z ≠ x) :
    z ∈ K ⊔ Uu := by
  have hWd : Order.krullDim (⊤ : LowerSet W.ogp) = (k + 1 : ℕ) + 1 :=
    W.krullDim_top_eq (by rw [hW])
  have hxd : Order.krullDim (LowerSet.Iic x) = k + 1 := by
    rw [LowerSet.krullDim_Iic, hx]
    rfl
  obtain ⟨hs, hi₁, hi₂⟩ := (isPastingIn_cond_iff α).1 hp
  have hz : z ∈ W.ogp.bdryFull ⊤ := (W.mem_bdryFull_top_iff z).2 hzt
  rw [bdryFull_eq_bdry_sup_bdry_not ⊤ α, bdry_eq_boundary hWd, bdry_eq_boundary hWd] at hz
  rcases hz with hz | hz
  · rw [← hs] at hz
    rcases hz with hz | hz
    · have hzx' : z ∈ W.ogp.bdryFull (LowerSet.Iic x) := by
        rw [← SetLike.mem_coe, bdryFull, coe_bdry_Iic_sup]
        exact lt_of_le_of_ne hz hzx
      rw [bdryFull_eq_bdry_sup_bdry_not _ α, bdry_eq_boundary hxd,
        bdry_eq_boundary hxd] at hzx'
      rcases hzx' with h | h
      · exact Or.inl (inf_le_right (a := LowerSet.Iic x) (hi₂ ▸ h))
      · refine Or.inr (hU ▸ boundary_le _ k (!α) ?_)
        have hc : W.ogp.boundary (W.ogp.boundary ⊤ (k + 1) α) k (!α) =
            W.ogp.boundary (LowerSet.Iic x) k (!α) :=
          IsPastingIn.boundary_cond (!α) (A := K) (B := LowerSet.Iic x)
            (by rw [Bool.cond_not, Bool.cond_not]; exact hp)
        rw [W.isMolecule.isGlobular k (k + 1) (Nat.lt_succ_self k) (!α) (!α)]
        rw [← hc, W.isMolecule.isGlobular k (k + 1) (Nat.lt_succ_self k) (!α) α] at h
        exact h
    · exact Or.inl hz
  · exact Or.inr (hU ▸ hz)

private theorem boundary_Iic_zero (hk : 0 < k)
    (hp : W.ogp.IsPastingIn k (cond α (LowerSet.Iic x) K) (cond α K (LowerSet.Iic x))
      (W.ogp.boundary ⊤ (k + 1) α))
    (hIg : W.ogp.IsGlobular (LowerSet.Iic x)) (hKg : W.ogp.IsGlobular K) :
    W.ogp.boundary (LowerSet.Iic x) 0 false = W.ogp.boundary ⊤ 0 false := by
  obtain ⟨hs, hi₁, hi₂⟩ := (isPastingIn_cond_iff α).1 hp
  have h₁ : W.ogp.boundary (LowerSet.Iic x) 0 false = W.ogp.boundary K 0 false := by
    rw [← hIg 0 k hk false α, ← hi₂, hi₁, hKg 0 k hk false (!α)]
  rw [← W.isMolecule.isGlobular 0 (k + 1) (Nat.succ_pos k) false α, ← hs,
    boundary_sup_of_boundary_eq h₁]

end Lattice

private theorem isPushout_realize_inclusion (P : RDCpx.{0}) {Λ L B D : LowerSet P.obj.toOGP}
    (hB : Λ ⊓ L = B) (hD : Λ ⊔ L = D) :
    IsPushout (realize.{u}.map (RDCpx.inclusion P (hB ▸ inf_le_left : B ≤ Λ)))
      (realize.map (RDCpx.inclusion P (hB ▸ inf_le_right : B ≤ L)))
      (realize.map (RDCpx.inclusion P (hD ▸ le_sup_left : Λ ≤ D)))
      (realize.map (RDCpx.inclusion P (hD ▸ le_sup_right : L ≤ D))) := by
  subst hB hD
  exact isPushout_realize_restrictInclOfSubset P Λ L

variable {S W : Atom} (e : S.ogp ⟶ W.ogp) (hx : e S.top ⋖ W.top)

private def faceHorn : LowerSet W.ogp :=
  hornSubset (atomicHornDataOfCovBy W (e S.top) hx).toHornData

private theorem mem_faceHorn_iff {z : W.ogp} :
    z ∈ faceHorn e hx ↔ z ≠ W.top ∧ z ≠ e S.top :=
  mem_hornSet_closure_singleton_iff _ rfl

include hx in
private theorem apply_ne_top (y : S.ogp) : e y ≠ W.top :=
  ((isMorphism e).monotone (S.le_top y)).trans_lt hx.lt |>.ne

private theorem mem_faceHorn_of_mem_bdryFull [IsInclusion e] {y : S.ogp}
    (hy : y ∈ S.ogp.bdryFull ⊤) :
    e y ∈ faceHorn e hx :=
  (mem_faceHorn_iff e hx).2 ⟨apply_ne_top e hx y,
    fun h => (S.mem_bdryFull_top_iff y).1 hy (IsInclusion.injective (f := e) h)⟩

private theorem incl_comp_mem_faceHorn [IsInclusion e] (y : S.ogp.restrict (S.ogp.bdryFull ⊤)) :
    (incl (S.ogp.bdryFull ⊤) ≫ e) y ∈ faceHorn e hx :=
  mem_faceHorn_of_mem_bdryFull e hx y.2

private theorem hornSubset_inf_map [IsInclusion e] :
    faceHorn e hx ⊓ OGP.map e ⊤ =
      OGP.map (incl (S.ogp.bdryFull ⊤) ≫ e) ⊤ := by
  refine SetLike.ext fun z => ⟨?_, ?_⟩
  · rintro ⟨hz, y, -, rfl⟩
    refine ⟨⟨y, (S.mem_bdryFull_top_iff y).2 fun h => ?_⟩, LowerSet.mem_top, rfl⟩
    exact ((mem_faceHorn_iff e hx).1 hz).2 (by rw [h])
  · rintro ⟨y, -, rfl⟩
    exact ⟨mem_faceHorn_of_mem_bdryFull e hx y.2, y.1, LowerSet.mem_top, rfl⟩

private theorem hornSubset_sup_map :
    faceHorn e hx ⊔ OGP.map e ⊤ =
      W.ogp.bdryFull ⊤ := by
  refine SetLike.ext fun z => ⟨?_, fun hz => ?_⟩
  · rintro (hz | ⟨y, -, rfl⟩)
    · exact (W.mem_bdryFull_top_iff z).2 ((mem_faceHorn_iff e hx).1 hz).1
    · exact (W.mem_bdryFull_top_iff _).2 (apply_ne_top e hx y)
  · by_cases hzx : z = e S.top
    · exact Or.inr ⟨S.top, LowerSet.mem_top, hzx.symm⟩
    · exact Or.inl ((mem_faceHorn_iff e hx).2 ⟨(W.mem_bdryFull_top_iff z).1 hz, hzx⟩)

private theorem isPushout_realize_horn [IsInclusion e] :
    IsPushout
      (realize.{u}.map (RDCpx.ofInclusion (P := S.toMoleculeShape.rdc.restrict (S.ogp.bdryFull ⊤))
        (Q := W.toMoleculeShape.rdc.restrict
          (faceHorn e hx))
        (codRestrict (incl (S.ogp.bdryFull ⊤) ≫ e) _ (incl_comp_mem_faceHorn e hx))))
      (realize.map (S.toMoleculeShape.rdc.restrictIncl (S.ogp.bdryFull ⊤)))
      (realize.map (RDCpx.inclusion W.toMoleculeShape.rdc
        (hornSubset_sup_map e hx ▸ le_sup_left)))
      (realize.map (RDCpx.ofInclusion (P := S.toMoleculeShape.rdc)
        (Q := W.toMoleculeShape.rdc.restrict (W.ogp.bdryFull ⊤))
        (codRestrict e _ fun y => (W.mem_bdryFull_top_iff _).2 (apply_ne_top e hx y)))) := by
  let iB : (S.toMoleculeShape.rdc.restrict (S.ogp.bdryFull ⊤)).obj.toOGP ⟶
      W.toMoleculeShape.rdc.obj.toOGP := incl (S.ogp.bdryFull ⊤) ≫ e
  refine (isPushout_realize_inclusion W.toMoleculeShape.rdc (hornSubset_inf_map e hx)
    (hornSubset_sup_map e hx)).of_iso (realize.mapIso (restrictIso iB).symm) (Iso.refl _)
    (realize.mapIso (restrictIso (U := S.toMoleculeShape.rdc) (R := W.toMoleculeShape.rdc) e).symm)
    (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp]
    congr 1
    rw [Iso.eq_inv_comp]
    ext
    rfl
  · rw [Functor.mapIso_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.symm_hom, ← Functor.map_comp,
      ← Functor.map_comp]
    congr 1
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    ext
    rfl
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp]
    congr 1
    rw [Iso.eq_inv_comp]
    ext
    rfl

private theorem mem_range_of_apply_top_mem {R P : RDCpx.{0}} {Y Z : DiagSet.{u}}
    (ψ : realize.obj R ⟶ Z) (m : Y ⟶ Z) (f : P.obj.toOGP ⟶ R.obj.toOGP) [IsInclusion f]
    (hf : ∃ g, g ≫ m = realize.map (RDCpx.ofInclusion f) ≫ ψ) {V : Atom}
    (s : atomToRDCpx.obj V ⟶ R) (hs : ConcreteCategory.hom s.hom V.top ∈ OGP.map f ⊤) :
    ψ.app (op V) ⟨s⟩ ∈ (Subfunctor.range m).obj (op V) := by
  obtain ⟨g, hg⟩ := hf
  have hr : (restrictIso f).inv ≫ RDCpx.ofInclusion f = R.restrictIncl (OGP.map f ⊤) := by
    rw [Iso.inv_comp_eq]
    ext
    rfl
  have he : s = (restrictLift R _ s (fun t => apply_mem_of_apply_top_mem s hs t) ≫
      (restrictIso f).inv) ≫ RDCpx.ofInclusion f := by
    rw [Category.assoc, hr, restrictLift, RDCpx.codRestrict_restrictIncl]
  refine ⟨g.app (op V) ⟨restrictLift R _ s (fun t => apply_mem_of_apply_top_mem s hs t) ≫
      (restrictIso f).inv⟩, ?_⟩
  exact (congrArg (fun φ => φ.app (op V) ⟨restrictLift R _ s
      (fun t => apply_mem_of_apply_top_mem s hs t) ≫ (restrictIso f).inv⟩) hg).trans
    (congrArg (fun c => ψ.app (op V) ⟨c⟩) he.symm)

private theorem exists_comp_eq_realize_inclusion {R P₁ P₂ : RDCpx.{0}} {Λ D : LowerSet R.obj.toOGP}
    (hΛ : Λ ≤ D) {Y Z : DiagSet.{u}} (ψ : realize.obj (R.restrict D) ⟶ Z) (m : Y ⟶ Z) [Mono m]
    (f₁ : P₁.obj.toOGP ⟶ (R.restrict D).obj.toOGP) (f₂ : P₂.obj.toOGP ⟶ (R.restrict D).obj.toOGP)
    [IsInclusion f₁] [IsInclusion f₂]
    (h₁ : ∃ g, g ≫ m = realize.map (RDCpx.ofInclusion f₁) ≫ ψ)
    (h₂ : ∃ g, g ≫ m = realize.map (RDCpx.ofInclusion f₂) ≫ ψ)
    (hcov : ∀ z (hz : z ∈ Λ), ⟨z, hΛ hz⟩ ∈ OGP.map f₁ ⊤ ∨ ⟨z, hΛ hz⟩ ∈ OGP.map f₂ ⊤) :
    ∃ φ, φ ≫ m = realize.map (RDCpx.inclusion R hΛ) ≫ ψ := by
  refine Subfunctor.exists_comp_eq_of_range_le m _ ?_
  rintro ⟨V⟩ _ ⟨⟨t⟩, rfl⟩
  have ht := (ConcreteCategory.hom t.hom V.top).2
  rcases hcov _ ht with h | h
  · exact mem_range_of_apply_top_mem ψ m f₁ h₁ _ h
  · exact mem_range_of_apply_top_mem ψ m f₂ h₂ _ h

private theorem ofInclusion_codRestrict_comp {P Q R : RDCpx.{0}} (f : P.obj.toOGP ⟶ Q.obj.toOGP)
    (g : Q.obj.toOGP ⟶ R.obj.toOGP) [IsInclusion f] [IsInclusion g] (C : LowerSet R.obj.toOGP)
    (h : ∀ a, g a ∈ C) (h' : ∀ a, (f ≫ g) a ∈ C) :
    RDCpx.ofInclusion (P := P) (Q := R.restrict C) (codRestrict (f ≫ g) C h') =
      RDCpx.ofInclusion f ≫ RDCpx.ofInclusion (P := Q) (Q := R.restrict C) (codRestrict g C h) := by
  ext
  rfl

section Face

variable {X Y : DiagSet.{u}} {S W : Atom} (e : S.ogp ⟶ W.ogp) [IsInclusion e]

omit [IsInclusion e] in
private theorem faceHorn_le_bdryFull (hx : e S.top ⋖ W.top) : faceHorn e hx ≤ W.ogp.bdryFull ⊤ :=
  hornSubset_sup_map e hx ▸ le_sup_left

private theorem face_spec {Pc P₁ P₂ : RDCpx.{0}} (c : Pc.obj.toOGP ⟶ W.ogp)
    (fI : S.ogp ⟶ Pc.obj.toOGP) (fK : P₁.obj.toOGP ⟶ Pc.obj.toOGP) (eU : P₂.obj.toOGP ⟶ W.ogp)
    [IsInclusion c] [IsInclusion fI] [IsInclusion fK] [IsInclusion eU]
    (hc : ∀ a, c a ∈ W.ogp.bdryFull ⊤) (hU' : ∀ a, eU a ∈ W.ogp.bdryFull ⊤)
    (ψ : realize.obj (W.toMoleculeShape.rdc.restrict (W.ogp.bdryFull ⊤)) ⟶ Y)
    (v : realize.obj Pc ⟶ Y) (m : X ⟶ Y) [Mono m]
    (hψ : realize.map (RDCpx.ofInclusion (P := Pc)
      (Q := W.toMoleculeShape.rdc.restrict (W.ogp.bdryFull ⊤)) (codRestrict c _ hc)) ≫ ψ = v)
    (hKm : ∃ g, g ≫ m = realize.map (RDCpx.ofInclusion fK) ≫ v)
    (hUm : ∃ g, g ≫ m = realize.map (RDCpx.ofInclusion (P := P₂)
      (Q := W.toMoleculeShape.rdc.restrict (W.ogp.bdryFull ⊤)) (codRestrict eU _ hU')) ≫ ψ)
    {k : ℕ} (α : Bool) (hW : W.dimension = k + 2) (hS : S.dimension = k + 1)
    (hp : W.ogp.IsPastingIn k (cond α (OGP.map (fI ≫ c) ⊤) (OGP.map (fK ≫ c) ⊤))
      (cond α (OGP.map (fK ≫ c) ⊤) (OGP.map (fI ≫ c) ⊤)) (W.ogp.boundary ⊤ (k + 1) α))
    (hU : OGP.map eU ⊤ = W.ogp.boundary ⊤ (k + 1) (!α)) :
    ∃ hx : (fI ≫ c) S.top ⋖ W.top,
      (∃ φ, φ ≫ m = realize.map (RDCpx.inclusion _ (faceHorn_le_bdryFull (fI ≫ c) hx)) ≫ ψ) ∧
      realize.map (RDCpx.ofInclusion (P := S.toMoleculeShape.rdc)
        (Q := W.toMoleculeShape.rdc.restrict (W.ogp.bdryFull ⊤))
        (codRestrict (fI ≫ c) _ fun a => (W.mem_bdryFull_top_iff _).2
          (apply_ne_top (fI ≫ c) hx a))) ≫ ψ =
        realize.map (RDCpx.ofInclusion fI) ≫ v ∧
      (0 < k → W.ogp.IsGlobular (OGP.map (fK ≫ c) ⊤) →
        W.ogp.boundary (LowerSet.Iic ((fI ≫ c) S.top)) 0 false = W.ogp.boundary ⊤ 0 false) := by
  have hr {Q : RDCpx.{0}} (f : Q.obj.toOGP ⟶ Pc.obj.toOGP) [IsInclusion f]
      (h : ∀ a, (f ≫ c) a ∈ W.ogp.bdryFull ⊤) :
      realize.map (RDCpx.ofInclusion (P := Q)
        (Q := W.toMoleculeShape.rdc.restrict (W.ogp.bdryFull ⊤)) (codRestrict (f ≫ c) _ h)) ≫ ψ =
        realize.map (RDCpx.ofInclusion f) ≫ v :=
    (congrArg (fun t => realize.map t ≫ ψ) (ofInclusion_codRestrict_comp (P := Q) (Q := Pc)
      (R := W.toMoleculeShape.rdc) f c _ hc h)).trans
      ((congrArg (· ≫ ψ) (realize.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        (congrArg (realize.map (RDCpx.ofInclusion f) ≫ ·) hψ)))
  have hKc : ∀ a, (fK ≫ c) a ∈ W.ogp.bdryFull ⊤ := fun a => hc (fK a)
  have hI : OGP.map (fI ≫ c) ⊤ = LowerSet.Iic ((fI ≫ c) S.top) := by
    rw [← S.Iic_top, map_Iic]
  have hg : grade ℕ ((fI ≫ c) S.top) = k + 1 := by
    rw [(isMorphism (fI ≫ c)).grade_eq, ← S.dimension_eq, hS]
  have hx : (fI ≫ c) S.top ⋖ W.top := GradeOrder.covBy_of_le_of_grade_eq_add_one (W.le_top _)
    (by rw [← W.dimension_eq, hg, hW])
  rw [hI] at hp
  obtain ⟨g, hg'⟩ := hKm
  refine ⟨hx, exists_comp_eq_realize_inclusion (R := W.toMoleculeShape.rdc) _ ψ m
    (codRestrict (fK ≫ c) _ hKc) (codRestrict eU _ hU') ⟨g, hg'.trans (hr fK hKc).symm⟩ hUm
    fun z hz => ?_, hr (Q := S.toMoleculeShape.rdc) fI _, fun hk hKg => ?_⟩
  · rcases mem_sup_of_ne W α hW hg hp hU ((mem_faceHorn_iff _ hx).1 hz).1
      ((mem_faceHorn_iff _ hx).1 hz).2 with ⟨y, -, rfl⟩ | ⟨y, -, rfl⟩
    · exact Or.inl ⟨y, LowerSet.mem_top, rfl⟩
    · exact Or.inr ⟨y, LowerSet.mem_top, rfl⟩
  · exact boundary_Iic_zero W α hk hp
      (hI ▸ (isGlobular_map_iff (fI ≫ c) ⊤).2 S.isMolecule.isGlobular) hKg

end Face

variable {X Y : DiagSet.{u}}

private theorem exists_comp_eq_unit_map (u : PastingDiagram X) (m : X ⟶ Y) (k : ℕ) (α : Bool) :
    ∃ g, g ≫ m = ((u.mapTo m).boundary k α).unit.map :=
  ⟨((u.boundary k α).unit).map, (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _))⟩

private theorem closedSubpresheafRealizeIso_hom_ι (U : Atom) (S : LowerSet U.ogp) :
    (closedSubpresheafRealizeIso.{u} U S).hom ≫ (closedSubpresheaf U S).ι =
      realize.map (U.toMoleculeShape.rdc.restrictIncl S) ≫ (realizeAtomIso U).hom := by
  ext ⟨T⟩ ⟨c⟩
  rfl

private theorem ι_attach (c : CellularExtensionData Y) (e : c.ι) :
    Sigma.ι (fun e => realize.{u}.obj
      ((c.shape e).toMoleculeShape.rdc.restrict ((c.shape e).ogp.bdryFull ⊤))) e ≫ c.attach =
      (c.parallel e).sphere :=
  Sigma.ι_desc _ _

namespace InversionData

variable (A : InversionData X)

private theorem exists_face_side (i : A.ι) (α : Bool) :
    ∃ (e : (A.inverseExtension.shape (i, α)).ogp ⟶ (A.invertorExtension.shape (i, α)).ogp)
      (_ : IsInclusion e) (hx : e (A.inverseExtension.shape (i, α)).top ⋖
        (A.invertorExtension.shape (i, α)).top),
      (∃ φ, φ ≫ A.inverseExtension.incl = realize.map (RDCpx.inclusion _
        (faceHorn_le_bdryFull e hx)) ≫ (A.invertorExtension.parallel (i, α)).sphere) ∧
      realize.map (RDCpx.ofInclusion (P := (A.inverseExtension.shape (i, α)).toMoleculeShape.rdc)
        (Q := (A.invertorExtension.shape (i, α)).toMoleculeShape.rdc.restrict
          ((A.invertorExtension.shape (i, α)).ogp.bdryFull ⊤))
        (codRestrict e _ fun y => ((A.invertorExtension.shape (i, α)).mem_bdryFull_top_iff _).2
          (apply_ne_top e hx y))) ≫ (A.invertorExtension.parallel (i, α)).sphere =
        (ofCell (A.inverseExtension.cell (i, α))).map ∧
      (1 < (A.shape i).dimension →
        (A.invertorExtension.shape (i, α)).ogp.boundary
          (LowerSet.Iic (e (A.inverseExtension.shape (i, α)).top)) 0 false =
          (A.invertorExtension.shape (i, α)).ogp.boundary ⊤ 0 false) := by
  let D := A.inverseData i
  have hcomp : (cond α (A.invertorExtension.target (i, α))
      (A.invertorExtension.source (i, α))).toPastingDiagram =
      (cond α (D.inverse α).toPastingDiagram D.cell.toPastingDiagram).paste
        (cond α D.cell.toPastingDiagram (D.inverse α).toPastingDiagram) (D.cell.dim - 1)
        (D.pastable α) := by
    cases α <;> rfl
  have hunit : (cond (!α) (A.invertorExtension.target (i, α))
      (A.invertorExtension.source (i, α))).toPastingDiagram = (D.unitBdry α).toPastingDiagram := by
    cases α <;> rfl
  let P := A.invertorExtension.parallel (i, α)
  have hd := D.dim_pos
  have hcd : (A.shape i).dimension = D.cell.dim := rfl
  have hv : (A.invertorExtension.source (i, α)).dim = D.cell.dim - 1 + 1 :=
    (D.dim_source α).trans (Nat.sub_add_cancel hd).symm
  have hm (β : Bool) (a) : P.cellShapeEmb β a ∈ P.cellShape.ogp.bdryFull ⊤ :=
    P.map_cellShapeEmb_le_bdryFull β ⟨a, LowerSet.mem_top, rfl⟩
  let wP := Within.ofEquiv
    (PastingDiagram.equiv_of_eq ((P.restrictAlong_sphere α).trans hcomp).symm)
  let wU := Within.ofEquiv (PastingDiagram.equiv_of_eq ((P.restrictAlong_sphere (!α)).trans hunit))
  obtain ⟨wI, hp₀⟩ := Within.exists_isPastingIn_pasteIn α (D.pastable α)
  have hmap {a : PastingDiagram _} (w : Within a _) :
      OGP.map (wP.emb ≫ P.cellShapeEmb α) w.image =
        OGP.map ((w.trans wP).emb ≫ P.cellShapeEmb α) ⊤ :=
    (map_comp w.emb _ ⊤).symm.trans
      (congrArg (OGP.map · ⊤) (Category.assoc w.emb wP.emb (P.cellShapeEmb α)).symm)
  have htop : OGP.map (wP.emb ≫ P.cellShapeEmb α) ⊤ =
      P.cellShape.ogp.boundary ⊤ (D.cell.dim - 1 + 1) α := by
    rw [map_comp, ← hv, ← P.map_cellShapeEmb α]
    exact congrArg (OGP.map _) (Within.image_ofEquiv _)
  have hp := (isPastingIn_map_iff (wP.emb ≫ P.cellShapeEmb α) _ _ _ ⊤).2 hp₀
  rw [Bool.apply_cond (OGP.map (wP.emb ≫ P.cellShapeEmb α)),
    Bool.apply_cond (OGP.map (wP.emb ≫ P.cellShapeEmb α)), hmap, hmap, htop] at hp
  obtain ⟨g, hg⟩ := exists_comp_eq_unit_map (ofCell (A.cell i)) A.inverseExtension.incl
    (D.cell.dim - 1) α
  obtain ⟨hx, hφ, hr, hs⟩ := face_spec (S := A.inverseExtension.shape (i, α))
    (W := A.invertorExtension.shape (i, α))
    (Pc := (cond α (A.invertorExtension.target (i, α)).shape
      (A.invertorExtension.source (i, α)).shape).rdc) (P₁ := D.cell.shape.rdc)
    (P₂ := (cond (!α) (A.invertorExtension.target (i, α)).shape
      (A.invertorExtension.source (i, α)).shape).rdc)
    (P.cellShapeEmb α) (wI.trans wP).emb ((Within.pasteIn α (D.pastable α)).trans wP).emb
    (P.cellShapeEmb (!α)) (hm α) (hm (!α)) P.sphere _ A.inverseExtension.incl rfl
    ⟨(ofCell (A.cell i)).map, ((Within.pasteIn α (D.pastable α)).trans wP).comm.symm⟩
    ⟨_, (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hg).trans wU.comm)⟩
    (k := D.cell.dim - 1) α ((A.invertorExtension.dimension_shape _).trans (by rw [hv]))
    ((A.dimension_inverseExtension_shape (i, α)).trans
      (hcd.trans (Nat.sub_add_cancel hd).symm)) hp
    ((P.map_cellShapeEmb (!α)).trans (congrArg (P.cellShape.ogp.boundary ⊤ · (!α)) hv))
  exact ⟨_, inferInstance, hx, hφ, hr.trans (wI.trans wP).comm,
    fun h => hs (Nat.sub_pos_of_lt (hcd ▸ h))
      ((isGlobular_map_iff _ ⊤).2 D.cell.shape.isMolecule.isGlobular)⟩

private theorem exists_face (j : A.ι × Bool) :
    ∃ (e : (A.inverseExtension.shape j).ogp ⟶ (A.invertorExtension.shape j).ogp)
      (_ : IsInclusion e) (hx : e (A.inverseExtension.shape j).top ⋖
        (A.invertorExtension.shape j).top),
      (∃ φ, φ ≫ A.inverseExtension.incl = realize.map (RDCpx.inclusion _
        (faceHorn_le_bdryFull e hx)) ≫ (A.invertorExtension.parallel j).sphere) ∧
      realize.map (RDCpx.ofInclusion (P := (A.inverseExtension.shape j).toMoleculeShape.rdc)
        (Q := (A.invertorExtension.shape j).toMoleculeShape.rdc.restrict
          ((A.invertorExtension.shape j).ogp.bdryFull ⊤))
        (codRestrict e _ fun y => ((A.invertorExtension.shape j).mem_bdryFull_top_iff _).2
          (apply_ne_top e hx y))) ≫ (A.invertorExtension.parallel j).sphere =
        (ofCell (A.inverseExtension.cell j)).map ∧
      (1 < (A.shape j.1).dimension →
        (A.invertorExtension.shape j).ogp.boundary
          (LowerSet.Iic (e (A.inverseExtension.shape j).top)) 0 false =
          (A.invertorExtension.shape j).ogp.boundary ⊤ 0 false) :=
  A.exists_face_side j.1 j.2

private theorem isPushout_of_left {Z₁ Z₂ Z₃ Z₄ Y E : DiagSet.{u}} {f : Z₁ ⟶ Z₂} {g : Z₁ ⟶ Z₃}
    {h : Z₂ ⟶ Z₄} {k : Z₃ ⟶ Z₄} {a : Z₁ ⟶ Y} {i : Y ⟶ E} {r : Z₃ ⟶ E}
    (T : IsPushout f g h k) (P : IsPushout a g i r) (φ : Z₂ ⟶ Y) (ψ : Z₄ ⟶ E)
    (hφ : f ≫ φ = a) (hψ : k ≫ ψ = r) (p : φ ≫ i = h ≫ ψ) : IsPushout φ h i ψ :=
  IsPushout.of_left (by rw [hφ, hψ]; exact P) p T

private noncomputable def inverseFace (j : A.ι × Bool) :
    (A.inverseExtension.shape j).ogp ⟶ (A.invertorExtension.shape j).ogp :=
  (A.exists_face j).choose

private instance isInclusion_inverseFace (j : A.ι × Bool) : IsInclusion (A.inverseFace j) :=
  (A.exists_face j).choose_spec.fst

private theorem inverseFace_covBy (j : A.ι × Bool) :
    A.inverseFace j (A.inverseExtension.shape j).top ⋖ (A.invertorExtension.shape j).top :=
  (A.exists_face j).choose_spec.snd.fst

noncomputable def invertorHorn (j : A.ι × Bool) : AtomicHornData :=
  atomicHornDataOfCovBy (A.invertorExtension.shape j) _ (A.inverseFace_covBy j)

private noncomputable def hornRestrict (j : A.ι × Bool) :
    realize.obj ((A.invertorExtension.shape j).toMoleculeShape.rdc.restrict
      (faceHorn (A.inverseFace j) (A.inverseFace_covBy j))) ⟶ X :=
  (A.exists_face j).choose_spec.snd.snd.1.choose

private theorem hornRestrict_comp (j : A.ι × Bool) :
    A.hornRestrict j ≫ A.inverseExtension.incl = realize.map (RDCpx.inclusion _
      (faceHorn_le_bdryFull (A.inverseFace j) (A.inverseFace_covBy j))) ≫
        (A.invertorExtension.parallel j).sphere :=
  (A.exists_face j).choose_spec.snd.snd.1.choose_spec

private theorem inverseFace_sphere (j : A.ι × Bool) :
    realize.map (RDCpx.ofInclusion (P := (A.inverseExtension.shape j).toMoleculeShape.rdc)
        (Q := (A.invertorExtension.shape j).toMoleculeShape.rdc.restrict
          ((A.invertorExtension.shape j).ogp.bdryFull ⊤))
        (codRestrict (A.inverseFace j) _ fun y =>
          ((A.invertorExtension.shape j).mem_bdryFull_top_iff _).2
            (apply_ne_top (A.inverseFace j) (A.inverseFace_covBy j) y))) ≫
      (A.invertorExtension.parallel j).sphere =
      (ofCell (A.inverseExtension.cell j)).map :=
  (A.exists_face j).choose_spec.snd.snd.2.1

noncomputable def hornAttach : (∐ fun j => horn.{u} (A.invertorHorn j).toHornData) ⟶ X :=
  Sigma.desc fun j => (closedSubpresheafRealizeIso (A.invertorExtension.shape j) _).inv ≫
    A.hornRestrict j

noncomputable def hornFill : (∐ fun j => ball.{u} (A.invertorHorn j).atom) ⟶ A.step :=
  Sigma.desc fun j => (realizeAtomIso (A.invertorExtension.shape j)).inv ≫
    (ofCell (A.invertorExtension.cell j)).map

theorem isPushout_step :
    IsPushout A.hornAttach
      (Limits.Sigma.map fun j => hornInclusion.{u} (A.invertorHorn j).toHornData)
      A.stepIncl A.hornFill := by
  have T := isPushout_sigma_map
    (Z₁ := fun j => realize.{u}.obj ((A.inverseExtension.shape j).toMoleculeShape.rdc.restrict
      ((A.inverseExtension.shape j).ogp.bdryFull ⊤)))
    (Z₂ := fun j => realize.{u}.obj ((A.invertorExtension.shape j).toMoleculeShape.rdc.restrict
      (faceHorn (A.inverseFace j) (A.inverseFace_covBy j))))
    (Z₃ := fun j => realize.{u}.obj (A.inverseExtension.shape j).toMoleculeShape.rdc)
    (Z₄ := fun j => realize.{u}.obj ((A.invertorExtension.shape j).toMoleculeShape.rdc.restrict
      ((A.invertorExtension.shape j).ogp.bdryFull ⊤)))
    fun j => isPushout_realize_horn (A.inverseFace j) (A.inverseFace_covBy j)
  have t := (isPushout_of_left T
    (IsPushout.of_hasPushout A.inverseExtension.attach A.inverseExtension.bdryInclSigma)
    (Sigma.desc A.hornRestrict) A.invertorExtension.attach ?_ ?_ ?_).paste_vert
    (IsPushout.of_hasPushout A.invertorExtension.attach A.invertorExtension.bdryInclSigma)
  · refine t.of_iso (Sigma.mapIso fun j => closedSubpresheafRealizeIso.{u}
      (A.invertorExtension.shape j) (faceHorn (A.inverseFace j) (A.inverseFace_covBy j)))
      (Iso.refl _) (Sigma.mapIso fun j => realizeAtomIso.{u} (A.invertorExtension.shape j))
      (Iso.refl _) ?_ ?_ ?_ ?_
    · refine Sigma.hom_ext _ _ fun j => ?_
      have h₁ : Sigma.ι (fun j => horn.{u} (A.invertorHorn j).toHornData) j ≫ A.hornAttach =
          (closedSubpresheafRealizeIso _ _).inv ≫ A.hornRestrict j :=
        Sigma.ι_desc _ _
      have h₂ := Limits.Sigma.ι_map (fun j => (closedSubpresheafRealizeIso.{u}
        (A.invertorExtension.shape j) (faceHorn (A.inverseFace j) (A.inverseFace_covBy j))).hom) j
      exact (Sigma.ι_desc_assoc _ _ _).trans ((Category.comp_id _).trans
        ((Iso.hom_inv_id_assoc _ _).symm.trans ((congrArg (_ ≫ ·) h₁.symm).trans
          (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ A.hornAttach) h₂.symm)).trans
            (Category.assoc _ _ _)))))
    · refine Sigma.hom_ext _ _ fun j => ?_
      simp only [Category.assoc, Limits.Sigma.ι_map_assoc, CellularExtensionData.bdryInclSigma]
      have h₁ := Sigma.ι_mapIso_hom (fun j => realizeAtomIso.{u} (A.invertorExtension.shape j)) j
      have h₂ := Limits.Sigma.ι_map (fun j => hornInclusion.{u} (A.invertorHorn j).toHornData) j
      have hc := closedSubpresheafRealizeIso_hom_ι.{u} (A.invertorExtension.shape j)
        (faceHorn (A.inverseFace j) (A.inverseFace_covBy j))
      have hr := congrArg realize.{u}.map (RDCpx.inclusion_restrictIncl
        (A.invertorExtension.shape j).toMoleculeShape.rdc
        (faceHorn_le_bdryFull (A.inverseFace j) (A.inverseFace_covBy j)))
      rw [Functor.map_comp] at hr
      exact (congrArg (_ ≫ _ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hr).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) hc.symm).trans ((Category.assoc _ _ _).trans
            ((congrArg (_ ≫ ·) h₂.symm).trans
              (Sigma.ι_mapIso_hom_assoc (g := fun j => horn.{u} (A.invertorHorn j).toHornData)
                (fun j => closedSubpresheafRealizeIso.{u} (A.invertorExtension.shape j)
                  (faceHorn (A.inverseFace j) (A.inverseFace_covBy j))) j _).symm))))))
    · rfl
    · refine Sigma.hom_ext _ _ fun j => ?_
      have h₁ : Sigma.ι (fun j => ball.{u} (A.invertorHorn j).atom) j ≫ A.hornFill =
          (realizeAtomIso _).inv ≫ (ofCell (A.invertorExtension.cell j)).map :=
        Sigma.ι_desc _ _
      have h₂ := Limits.Sigma.ι_map (fun j => (realizeAtomIso.{u}
        (A.invertorExtension.shape j)).hom) j
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
        ((CellularExtensionData.ofCell_cell_map _ _).symm.trans
          ((Iso.hom_inv_id_assoc _ _).symm.trans ((congrArg (_ ≫ ·) h₁.symm).trans
            (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ A.hornFill) h₂.symm)).trans
              (Category.assoc _ _ _)))))
  · refine Sigma.hom_ext _ _ fun j => ?_
    rw [← cancel_mono A.inverseExtension.incl, Category.assoc, Category.assoc,
      Limits.Sigma.ι_map_assoc, Sigma.ι_desc_assoc, hornRestrict_comp, ← Category.assoc,
      (isPushout_realize_horn (A.inverseFace j) (A.inverseFace_covBy j)).w, Category.assoc,
      A.inverseFace_sphere j,
      CellularExtensionData.realize_map_restrictIncl_comp_ofCell_cell_map]
    exact congrArg (· ≫ _) (ι_attach A.inverseExtension j).symm
  · refine Sigma.hom_ext _ _ fun j => ?_
    rw [Limits.Sigma.ι_map_assoc]
    refine (congrArg (_ ≫ ·) (ι_attach A.invertorExtension j)).trans ?_
    rw [A.inverseFace_sphere j, CellularExtensionData.ofCell_cell_map]
  · refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc]
    exact (A.hornRestrict_comp j).trans (congrArg (_ ≫ ·) (ι_attach A.invertorExtension j).symm)

private theorem sourceHorns_invertorHorn (hA : ∀ i, 1 < (A.shape i).dimension) (j : A.ι × Bool) :
    sourceHorns.{u} (hornInclusion (A.invertorHorn j).toHornData) := by
  unfold sourceHorns
  exact ofHoms.mk (Subtype.mk (⟨A.invertorExtension.shape j, A.inverseFace j _⟩ : Σ U : Atom, U.ogp)
    ⟨A.inverseFace_covBy j, (A.exists_face j).choose_spec.snd.snd.2.2 (hA j.1)⟩)

theorem saturation_sourceHorns_stepIncl (hA : ∀ i, 1 < (A.shape i).dimension) :
    saturation.{u} sourceHorns A.stepIncl := by
  have := IsCellularlyClosed.isStableUnderCoproducts.{u} (saturation.{u} sourceHorns.{u})
  exact (saturation.{u} sourceHorns).of_isPushout A.isPushout_step
    (MorphismProperty.colimMap _ fun ⟨j⟩ => le_saturation _ _ (A.sourceHorns_invertorHorn hA j))

private theorem one_lt_dimension_stage (hA : ∀ i, 1 < (A.shape i).dimension) :
    ∀ (n : ℕ) (i : (A.stage n).2.ι), 1 < ((A.stage n).2.shape i).dimension
  | 0, i => hA i
  | n + 1, j => lt_of_lt_of_eq (Nat.lt_succ_of_lt (one_lt_dimension_stage hA n j.1))
      ((A.stage n).2.dimension_next_shape j).symm

theorem saturation_sourceHorns_toLocalization (hA : ∀ i, 1 < (A.shape i).dimension) :
    saturation.{u} sourceHorns A.toLocalization := by
  have := IsStableUnderTransfiniteComposition.shrink₀ (saturation.{u} sourceHorns.{u})
  let c : (saturation.{u} sourceHorns.{u}).TransfiniteCompositionOfShape ℕ A.toLocalization :=
    { F := Functor.ofSequence fun n => (A.stage n).2.stepIncl
      isoBot := Iso.refl _
      incl := (colimit.cocone _).ι
      isColimit := colimit.isColimit _
      fac := Category.id_comp _
      map_mem := fun n _ => by
        have h : (Functor.ofSequence fun n => (A.stage n).2.stepIncl).map
            (homOfLE (Order.le_succ n)) = (A.stage n).2.stepIncl :=
          Functor.ofSequence_map_homOfLE_succ _ n
        rw [h]
        exact (A.stage n).2.saturation_sourceHorns_stepIncl (A.one_lt_dimension_stage hA n) }
  exact transfiniteCompositionsOfShape_le _ ℕ _ (c.mem _)

end InversionData

theorem saturation_sourceHorns_toWalkingEquivalence (U : Atom) (hU : 1 < U.dimension) :
    saturation.{u} sourceHorns (toWalkingEquivalence.{u} U (zero_lt_one.trans hU)) :=
  (topInversionData U _).saturation_sourceHorns_toLocalization fun _ => hU

end Atoms.Diagrammatic
