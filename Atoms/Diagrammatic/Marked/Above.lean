import Atoms.Diagrammatic.Marked.ModelStructure
import Atoms.Homotopical.Marked.Cellular
import Atoms.Molecule.Construction.JoinSimplex

open CategoryTheory Limits MorphismProperty Opposite Order
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

namespace MarkedDiagSet

noncomputable def markedAboveFunctor (n : ℕ) : DiagSet.{u} ⥤ MarkedDiagSet.{u} where
  obj X := markedAbove X n
  map {X Y} f := Homotopical.MarkedPresheaf.homMk (X := markedAbove X n) (Y := markedAbove Y n) f
    fun V _ hx => (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx).imp_left
        (isDegenerate_app f))
  map_id _ := Homotopical.MarkedPresheaf.hom_ext rfl
  map_comp _ _ := Homotopical.MarkedPresheaf.hom_ext rfl

noncomputable def Coinductive.markedAboveFunctor (n : ℕ) : DiagSet.{u} ⥤ Coinductive n :=
  MarkedDiagSet.markedAboveFunctor n

theorem forget_map_markedAboveFunctor_map (n : ℕ) {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    Homotopical.MarkedPresheaf.forget.map ((markedAboveFunctor n).map f) = f :=
  rfl

theorem exists_app_eq_of_isPushout {A B C D : DiagSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ D} {inr : C ⟶ D} (h : IsPushout f g inl inr) {V : Atom} (y : D.obj (op V)) :
    (∃ b, inl.app (op V) b = y) ∨ ∃ c, inr.app (op V) c = y := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective _
    (isColimitOfPreserves ((evaluation _ _).obj (op V)) h.isColimit) y
  rcases j with (_ | _ | _)
  · exact Or.inl ⟨f.app (op V) x, hx⟩
  · exact Or.inl ⟨x, hx⟩
  · exact Or.inr ⟨x, hx⟩

theorem isPushout_markedAboveFunctor_map (n : ℕ) {A B C D : DiagSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ D} {inr : C ⟶ D} (h : IsPushout f g inl inr) :
    IsPushout ((markedAboveFunctor n).map f) ((markedAboveFunctor n).map g)
      ((markedAboveFunctor n).map inl) ((markedAboveFunctor n).map inr) := by
  have hw : (markedAboveFunctor n).map f ≫ (markedAboveFunctor n).map inl =
      (markedAboveFunctor n).map g ≫ (markedAboveFunctor n).map inr := by
    rw [← Functor.map_comp, h.w, Functor.map_comp]
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw)
    (Homotopical.MarkedPresheaf.isColimitOfForget _
      ((isColimitMapCoconePushoutCoconeEquiv _ hw).symm h.isColimit) fun V y hy => ?_)
  have key : ∀ y : D.obj (op V), (∃ b : B.obj (op V), b ∈ (markedAbove B n).marked V ∧
      inl.app (op V) b = y) ∨ (∃ c : C.obj (op V), c ∈ (markedAbove C n).marked V ∧
      inr.app (op V) c = y) → ∃ (j : WalkingSpan)
        (x : ((span ((markedAboveFunctor n).map f) ((markedAboveFunctor n).map g)).obj j
          ).underlying.obj (op V)),
        x ∈ ((span ((markedAboveFunctor n).map f) ((markedAboveFunctor n).map g)).obj j
          ).marked V ∧
        (Homotopical.MarkedPresheaf.forget.map
          ((PushoutCocone.mk _ _ hw).ι.app j)).app (op V) x = y := by
    rintro y (⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact ⟨WalkingSpan.left, b, hb, rfl⟩
    · exact ⟨WalkingSpan.right, c, hc, rfl⟩
  refine key y ?_
  rcases (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with
    ⟨W, p, z, hp, hni, rfl⟩ | hd
  · rcases exists_app_eq_of_isPushout h z with ⟨b, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨B.map p.op b, (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
        (Or.inl ⟨W, p, b, hp, hni, rfl⟩), NatTrans.naturality_apply inl p.op b⟩
    · exact Or.inr ⟨C.map p.op c, (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
        (Or.inl ⟨W, p, c, hp, hni, rfl⟩), NatTrans.naturality_apply inr p.op c⟩
  · rcases exists_app_eq_of_isPushout h y with ⟨b, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨b, (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 (Or.inr hd),
        rfl⟩
    · exact Or.inr ⟨c, (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 (Or.inr hd),
        rfl⟩

theorem mono_markedAboveFunctor_map (n : ℕ) {X Y : DiagSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono ((markedAboveFunctor n).map f) :=
  (Homotopical.MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono f))

end MarkedDiagSet

theorem boundary_stage_zero_eq {P : OGP.{0}} {m : ℕ} {X : LowerSet P}
    {L R M : ℕ → LowerSet P} (hs : P.IsStagedPasting m X L R M) (α : Bool) :
    ∀ i, 1 ≤ i → i ≤ m → P.boundary (M i) 0 α = P.boundary (M 1) 0 α := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rfl
    · obtain ⟨p₁, p₂⟩ := hs.stage_succ i (by omega)
      have hL := (hs.isMoleculeIn_left i (by omega)).1
      have hR := (hs.isMoleculeIn_right i (by omega)).1
      have hM := hs.isMoleculeIn_stage i (by omega)
      have hLM := p₁.isMoleculeIn hL hM
      rw [p₂.boundary_eq_of_lt_cond false hR.isGlobular hLM.isGlobular hi0,
        p₁.boundary_eq_of_lt_cond true hL.isGlobular hM.isGlobular hi0]
      exact ih (by omega) (by omega)

private theorem isDegenerate_or_dimension_eq {U : Atom} {S : LowerSet U.ogp} {V : Atom}
    (c : diagram (closedSubpresheaf.{u} U S).toFunctor V) :
    IsDegenerate _ c ∨ (Atom.map (c.1.down : V ⟶ U) ⊤ =
      LowerSet.Iic (ConcreteCategory.hom c.1.down V.top) ∧
        V.dimension = grade ℕ (ConcreteCategory.hom c.1.down V.top)) := by
  let f : V ⟶ U := c.1.down
  have hmem := apply_mem_closure_apply_top f
  have hp : IsCollapseHom (principalLift U _ f hmem) :=
    isCollapseHom_of_apply_eq_top _ (principalLift_apply_top f)
  by_cases hiso : IsIso (principalLift U _ f hmem)
  · refine Or.inr ⟨Atom.map_top f, ?_⟩
    rw [Atom.dimension_eq_of_iso (asIso (principalLift U _ f hmem)), Atom.dimension_ofClosure]
  · refine Or.inl ⟨_, principalLift U _ f hmem,
      ⟨⟨Atom.closureIncl U (f V.top)⟩, fun t => ?_⟩, hp, hiso, ?_⟩
    · exact S.lower (LowerSet.mem_Iic_iff.1 (closureIncl_mem_closure U _ t)) (c.2 V.top)
    · exact Subtype.ext (congrArg ULift.up (principalLift_comp_closureIncl U _ f hmem))

private theorem mem_marked_markedClosedSubset_iff {U : Atom} {S : LowerSet U.ogp} {A : Set U.ogp}
    (hA : ∀ a ∈ A, a ∈ S ∧ 0 < grade ℕ a) (hAS : ∀ a ∈ S, a ∈ A ↔ 1 < grade ℕ a) {V : Atom}
    (c : diagram.{u} (closedSubpresheaf U S).toFunctor V) :
    c ∈ (markedClosedSubset U S A hA).marked V ↔ IsDegenerate _ c ∨ 1 < V.dimension := by
  refine (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ _ _).trans ⟨?_, ?_⟩
  · rintro (h | ⟨a, ha, -, hd⟩)
    · exact Or.inl h
    · exact Or.inr (hd ▸ (hAS a (hA a ha).1).1 ha)
  · rintro (h | h)
    · exact Or.inl h
    · rcases isDegenerate_or_dimension_eq c with h' | ⟨him, hd⟩
      · exact Or.inl h'
      · exact Or.inr ⟨_, (hAS _ (c.2 V.top)).2 (hd ▸ h), him, hd⟩

private theorem isDegenerate_app_hom_iff {X Y : DiagSet.{u}} (e : X ≅ Y) {V : Atom}
    (x : diagram X V) : IsDegenerate Y (e.hom.app (op V) x) ↔ IsDegenerate X x := by
  refine ⟨fun h => ?_, isDegenerate_app e.hom⟩
  have hx : e.inv.app (op V) (e.hom.app (op V) x) = x :=
    congrFun (congrArg (fun φ : X ⟶ X => (φ.app (op V) : X.obj (op V) → X.obj (op V)))
      e.hom_inv_id) x
  exact hx ▸ isDegenerate_app e.inv h

private noncomputable def isoMarkedAboveOne {X : MarkedDiagSet.{u}}
    (hX : ∀ (V : Atom) (x : diagram X.underlying V),
      x ∈ X.marked V ↔ IsDegenerate _ x ∨ 1 < V.dimension)
    {Y : DiagSet.{u}} (e : X.underlying ≅ Y) : X ≅ (MarkedDiagSet.markedAboveFunctor 1).obj Y where
  hom := Homotopical.MarkedPresheaf.homMk (Y := MarkedDiagSet.markedAbove Y 1) e.hom
    fun V x hx => (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (((hX V x).1 hx).imp_left (isDegenerate_app_hom_iff e x).2)
  inv := Homotopical.MarkedPresheaf.homMk (X := MarkedDiagSet.markedAbove Y 1) e.inv
    fun V y hy => (hX V _).2
      (((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy).imp_left
        (isDegenerate_app_hom_iff e.symm y).2)
  hom_inv_id := Homotopical.MarkedPresheaf.hom_ext e.hom_inv_id
  inv_hom_id := Homotopical.MarkedPresheaf.hom_ext e.inv_hom_id

private def closedSubpresheafIsoOfEq (U : Atom) {S T : LowerSet U.ogp} (h : S = T) :
    (closedSubpresheaf.{u} U S).toFunctor ≅ (closedSubpresheaf U T).toFunctor :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun f => ⟨f.1, fun t => h ▸ f.2 t⟩
      invFun := fun f => ⟨f.1, fun t => h ▸ f.2 t⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (fun _ => rfl)

theorem exists_markedHornData_iso_markedAbove_hornInclusion (h : AtomicHornData)
    (x : h.atom.ogp) (hx : h.removed = LowerSet.Iic x)
    (hxU : ∀ α, h.atom.ogp.boundary (LowerSet.Iic x) 0 α = h.atom.ogp.boundary ⊤ 0 α) :
    ∃ m : MarkedHornData, Nonempty (Arrow.mk (markedHornInclusion.{u} m) ≅
      Arrow.mk ((MarkedDiagSet.markedAboveFunctor 1).map (hornInclusion h.toHornData))) := by
  have hface := mem_faceSet_top_of_isRewritableSubmolecule h.toHornData hx
  have hdx : grade ℕ x + 1 = h.atom.dimension := by
    rw [h.atom.dimension_eq, Nat.covBy_iff_add_one_eq.1 (hface.1.grade ℕ)]
  have hU : IsMoleculeIn h.atom.ogp ⊤ := h.atom.isMolecule
  have hd2 : 2 ≤ h.atom.dimension := by
    by_contra hlt
    have hx0 : grade ℕ x = 0 := by omega
    have hcl : ∀ α, h.atom.ogp.boundary (LowerSet.Iic x) 0 α = LowerSet.Iic x := fun α =>
      boundary_Iic_of_isMin (grade_eq_zero_iff.1 hx0) 0 α
    have h0 := krullDim_eq_zero_of_boundary_zero_eq hU
      (by rw [← hxU false, ← hxU true, hcl, hcl])
    rw [LowerSet.krullDim_top, h.atom.krullDim_eq_dimension] at h0
    have : h.atom.dimension = 0 := by exact_mod_cast h0
    have := h.positive
    omega
  have hV : h.atom.ogp.IsRewritableSubmolecule (.Iic x)
      (h.atom.ogp.boundary ⊤ (h.atom.dimension - 1) h.side) :=
    hx ▸ h.isRewritableSubmolecule_boundary
  obtain ⟨L, R, M, hs, hMn⟩ := exists_isStagedPasting_of_isSubmoleculeOf hV.isSubmoleculeOf
    (h.atom.dimension - 1) (krullDim_boundary_le _ _ _)
  have hbd : h.atom.ogp.boundary ⊤ (h.atom.dimension - 1) h.side = h.atom.ogp.bdry ⊤ h.side :=
    (h.atom.bdry_top_eq_boundary h.positive h.side).symm
  have hM1 : ∀ α, h.atom.ogp.boundary (M 1) 0 α = h.atom.ogp.boundary ⊤ 0 α := by
    intro α
    rw [← boundary_stage_zero_eq hs α _ (by omega) le_rfl, hMn,
      hU.isGlobular 0 (h.atom.dimension - 1) (by omega) α h.side]
  have p₁ : h.atom.ogp.IsPastingIn 0 (L 1) (M 0) (L 1 ⊔ M 0) := (hs.stage_succ 0 (by omega)).1
  have p₂ : h.atom.ogp.IsPastingIn 0 (L 1 ⊔ M 0) (R 1) (M 1) := (hs.stage_succ 0 (by omega)).2
  have hL1 : krullDim (L 1) = 0 := by
    refine krullDim_eq_zero_of_boundary_zero_eq (hs.isMoleculeIn_left 0 (by omega)).1 ?_
    rw [← p₁.boundary_input, ← p₂.boundary_input, hM1, ← hxU, ← hs.stage_zero,
      ← p₁.inf_eq_input, p₁.inf_eq_output]
  have hR1 : krullDim (R 1) = 0 := by
    refine krullDim_eq_zero_of_boundary_zero_eq (hs.isMoleculeIn_right 0 (by omega)).1 ?_
    rw [← p₂.inf_eq_input, p₂.inf_eq_output, p₁.boundary_output, hs.stage_zero, hxU, ← hM1,
      p₂.boundary_output]
  let hrew := h.atom.isRewritableSubmolecule_Iic_of_mem_faces hface
  let H := hrew.hornSet h.atom.isMolecule h.atom.isAtom.isRound
  let A : Set h.atom.ogp := {a ∈ H | 1 < grade ℕ a}
  have hA : ∀ a ∈ A, a ∈ H ∧ 0 < grade ℕ a := fun a ha => ⟨ha.1, by have := ha.2; omega⟩
  have hpt : ∀ {D : LowerSet h.atom.ogp}, krullDim D = 0 → ∀ y ∈ D, grade ℕ y ≠ 1 :=
    fun {D} hD y hy hyd => by
      have h1 : krullDim (LowerSet.Iic y) ≤ krullDim D :=
        LowerSet.krullDim_mono (LowerSet.Iic_le.2 hy)
      rw [LowerSet.krullDim_Iic, hD, hyd] at h1
      have : (1 : ℕ) ≤ 0 := by exact_mod_cast h1
      omega
  have hmarked : ∀ i < h.atom.dimension - 1,
      ∀ y ∈ L (i + 1) ⊔ R (i + 1), grade ℕ y = i + 1 → y ∈ A := by
    intro i hi y hy hyd
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [zero_add] at hy hyd
      rcases LowerSet.mem_sup_iff.1 hy with hy | hy
      · exact absurd hyd (hpt hL1 y hy)
      · exact absurd hyd (hpt hR1 y hy)
    have hyx : y ∉ LowerSet.Iic x := hs.notMem_of_mem_piece hi hy (by omega)
    have hyM : y ∈ M (h.atom.dimension - 1) :=
      hs.stage_le (i + 1) _ hi le_rfl (hs.left_sup_right_le_stage hi hy)
    rw [hMn, hbd] at hyM
    exact ⟨⟨bdry_le_bdryFull ⊤ h.side hyM, fun hyi => hyx hyi.1⟩, by omega⟩
  let m : MarkedHornData :=
    ⟨h.atom, h.positive, h.side, x, hface, A, hA, L, R, M, hs, hMn.trans hbd, hmarked⟩
  have hhorn : ∀ a, a ≠ h.atom.top → a ≠ x → a ∈ m.hornSet :=
    fun a ht hxa => m.mem_hornSet_iff.2 ⟨(h.atom.mem_bdryFull_top_iff a).2 ht, hxa⟩
  have hopp : ∀ y ∈ h.atom.ogp.faces (!h.side) h.atom.top, grade ℕ y = grade ℕ x ∧
      y ≠ h.atom.top ∧ y ≠ x := by
    intro y hy
    refine ⟨?_, hy.1.lt.ne, fun hyx => ?_⟩
    · have h₁ := Nat.covBy_iff_add_one_eq.1 (hy.1.grade ℕ)
      have h₂ := Nat.covBy_iff_add_one_eq.1 (hface.1.grade ℕ)
      omega
    · rw [hyx] at hy
      exact Bool.not_ne_self h.side (hy.2.symm.trans hface.2)
  have htm : ∀ a, a ∈ m.targetMarking ↔ 1 < grade ℕ a := by
    intro a
    rw [m.mem_targetMarking_iff]
    constructor
    · rintro (ha | ⟨hsub, ha⟩ | ha)
      · change a = h.atom.top at ha
        rw [ha, ← h.atom.dimension_eq]
        omega
      · obtain ⟨w, hw⟩ :=
          (h.atom.isMolecule.bdry (h.atom.krullDim_top_pos h.positive) (!h.side)).nonempty
        rw [← h.atom.Iic_top, bdry_Iic] at hw
        obtain ⟨y, hy, -⟩ := mem_lowerClosure.1 hw
        change a = x at ha
        rw [ha, ← (hopp y hy).1]
        exact (hsub hy).2
      · exact ha.2
    · intro ha
      by_cases ht : a = h.atom.top
      · exact Or.inl ht
      by_cases hax : a = x
      · refine Or.inr (Or.inl ⟨fun y hy => ⟨hhorn y (hopp y hy).2.1 (hopp y hy).2.2, ?_⟩, hax⟩)
        rw [(hopp y hy).1, ← hax]
        exact ha
      · exact Or.inr (Or.inr ⟨hhorn a ht hax, ha⟩)
  have hsrc : ∀ (V : Atom) (c : diagram m.source.underlying V),
      c ∈ m.source.marked V ↔ IsDegenerate _ c ∨ 1 < V.dimension := fun V c =>
    mem_marked_markedClosedSubset_iff hA (fun a ha => ⟨fun ha' => ha'.2, fun ha' => ⟨ha, ha'⟩⟩) c
  have htgt : ∀ (V : Atom) (c : diagram m.target.underlying V),
      c ∈ m.target.marked V ↔ IsDegenerate _ c ∨ 1 < V.dimension := fun V c =>
    mem_marked_markedClosedSubset_iff m.targetMarking_mem (fun a _ => htm a) c
  have hS : m.hornSet = hornSubset h.toHornData := SetLike.ext fun a =>
    (mem_hornSubset_iff m.toHornData a).trans
      ((by rw [hx]; exact Iff.rfl : _ ↔ a ≠ h.atom.top ∧ a ∉ h.atom.ogp.interior h.removed).trans
        (mem_hornSubset_iff h.toHornData a).symm)
  exact ⟨m, ⟨Arrow.isoMk (isoMarkedAboveOne hsrc (closedSubpresheafIsoOfEq h.atom hS))
    (isoMarkedAboveOne htgt (closedSubpresheafUnivIso h.atom))
    (Homotopical.MarkedPresheaf.hom_ext rfl)⟩⟩

end Atoms.Diagrammatic
