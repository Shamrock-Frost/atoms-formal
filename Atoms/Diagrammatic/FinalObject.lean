import Atoms.Diagrammatic.Suspension.Hom
import Atoms.Homotopical.Simplicial.FinalObject

open CategoryTheory Limits Opposite Simplicial MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open scoped ReversiblePathSpace

variable {X Y : DiagSet.{u}}

def DiagSet.IsContractible (G : DiagSet.{u}) : Prop :=
  WeakEquivalence ((DiagSet.toInfty 0).map (isTerminalBallAtomPoint.from G))

theorem DiagSet.isContractible_iff_of_weakEquivalence {G H : DiagSet.{u}} (g : G ⟶ H)
    [WeakEquivalence ((DiagSet.toInfty 0).map g)] : G.IsContractible ↔ H.IsContractible := by
  have hg : isTerminalBallAtomPoint.from G = g ≫ isTerminalBallAtomPoint.from H :=
    isTerminalBallAtomPoint.hom_ext _ _
  rw [DiagSet.IsContractible, DiagSet.IsContractible, hg, Functor.map_comp]
  exact ⟨fun _ => weakEquivalence_of_precomp ((DiagSet.toInfty 0).map g) _,
    fun _ => inferInstance⟩

def DiagSet.HasContractibleHoms (X : DiagSet.{u}) (α : Bool) (t : X.Vertex) :
    Prop :=
  ∀ x, (bipointedHom.obj (X.bipoint (cond α x t) (cond α t x))).IsContractible

def DiagSet.IsFinalObject (X : DiagSet.{u}) (t : X.Vertex) : Prop :=
  X.HasContractibleHoms true t

def DiagSet.IsInitialObject (X : DiagSet.{u}) (t : X.Vertex) : Prop :=
  X.HasContractibleHoms false t

def DiagSet.IsZeroObject (X : DiagSet.{u}) (t : X.Vertex) : Prop :=
  ∀ α, X.HasContractibleHoms α t

theorem DiagSet.isContractible_bipointedHom_iff_of_cylinder (hX : IsInftyCategory 1 X)
    (h₁ h₂ : (reversiblePathSpace.obj X).Vertex) :
    (bipointedHom.obj (X.bipoint (h₁.map ((π̃ false).app X))
      (h₂.map ((π̃ false).app X)))).IsContractible ↔
    (bipointedHom.obj (X.bipoint (h₁.map ((π̃ true).app X))
      (h₂.map ((π̃ true).app X)))).IsContractible := by
  have key (α : Bool) :
      (bipointedHom.obj ((reversiblePathSpace.obj X).bipoint h₁ h₂)).IsContractible ↔
      (bipointedHom.obj (X.bipoint (h₁.map ((π̃ α).app X))
        (h₂.map ((π̃ α).app X)))).IsContractible :=
    haveI := weakEquivalence_toInfty_map_of_rlp_monomorphisms 0
      (rlp_monomorphisms_bipointedHom_map (DiagSet.bipointMap ((π̃ α).app X) h₁ h₂)
        (rlp_monomorphisms_reversiblePathEndpoint_app 1 hX α))
    DiagSet.isContractible_iff_of_weakEquivalence
      (bipointedHom.map (DiagSet.bipointMap ((π̃ α).app X) h₁ h₂))
  exact (key false).symm.trans (key true)

theorem DiagSet.isContractible_bipointedHom_map_iff (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)]
    (a b : X.Vertex) :
    (bipointedHom.obj (Y.bipoint (a.map F)
      (b.map F))).IsContractible ↔
    (bipointedHom.obj (X.bipoint a b)).IsContractible :=
  haveI := @weakEquivalence_bipointedHom_map _ _ (DiagSet.bipointMap F a b) hX hY
    ‹WeakEquivalence ((DiagSet.toInfty 1).map F)›
  (DiagSet.isContractible_iff_of_weakEquivalence
    (bipointedHom.map (DiagSet.bipointMap F a b))).symm

private theorem exists_app_eq_of_rlp_monomorphisms {A B : DiagSet.{u}} {g : A ⟶ B}
    (hg : (monomorphisms DiagSet.{u}).rlp g) (b : B.Vertex) :
    ∃ a : A.Vertex, a.map g = b := by
  have := hg (initial.to (ball.{u} atomPoint)) (monomorphisms.infer_property _)
  have sq : CommSq (initial.to A) (initial.to (ball.{u} atomPoint)) g (vertexHom b) :=
    ⟨initial.hom_ext _ _⟩
  refine ⟨uliftYonedaEquiv (X := atomSimplex 0) (F := A) sq.lift, ?_⟩
  refine (uliftYonedaEquiv_comp (F := A) sq.lift g).symm.trans ?_
  rw [sq.fac_right, uliftYonedaEquiv_vertexHom]

private theorem exists_reversibleCylinder_of_weakEquivalence (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)]
    (y : Y.Vertex) :
    ∃ (x : X.Vertex) (c : (reversiblePathSpace.obj Y).Vertex),
      c.map ((π̃ false).app Y) = x.map F ∧
        c.map ((π̃ true).app Y) = y := by
  obtain ⟨v, hv⟩ := exists_app_eq_of_rlp_monomorphisms
    (rlp_monomorphisms_reversibleMappingPathSpaceProj F 1 hX hY) y
  refine ⟨DiagSet.Vertex.map (pullback.fst F ((π̃ false).app Y)) v,
    DiagSet.Vertex.map (pullback.snd F ((π̃ false).app Y)) v, ?_, ?_⟩
  · simp only [DiagSet.Vertex.map, ← NatTrans.comp_app_apply, pullback.condition]
  · rw [← hv]
    simp only [DiagSet.Vertex.map, reversibleMappingPathSpaceProj, ← NatTrans.comp_app_apply]

theorem DiagSet.hasContractibleHoms_map_iff (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)] (α : Bool)
    (t : X.Vertex) :
    Y.HasContractibleHoms α (t.map F) ↔ X.HasContractibleHoms α t := by
  have hmap (x : X.Vertex) :
      (bipointedHom.obj (Y.bipoint (cond α (x.map F)
        (t.map F)) (cond α (t.map F)
          (x.map F)))).IsContractible ↔
        (bipointedHom.obj (X.bipoint (cond α x t) (cond α t x))).IsContractible := by
    rw [← Bool.apply_cond (DiagSet.Vertex.map F),
      ← Bool.apply_cond (DiagSet.Vertex.map F)]
    exact DiagSet.isContractible_bipointedHom_map_iff hX hY F _ _
  refine ⟨fun h x => (hmap x).1 (h _), fun h y => ?_⟩
  obtain ⟨x, c, hc₀, hc₁⟩ := exists_reversibleCylinder_of_weakEquivalence hX hY F y
  set k := (t.map F).map ((ν̃).app Y)
  have hk (β : Bool) : k.map ((π̃ β).app Y) =
      t.map F := by
    have e : (ν̃).app Y ≫ (π̃ β).app Y = 𝟙 Y :=
      reversibleCylinder.pathConstant_app_comp_pathEndpoint_app _ β Y
    simp only [k, DiagSet.Vertex.map, ← NatTrans.comp_app_apply, Category.assoc, e]
    rfl
  have hcyl := DiagSet.isContractible_bipointedHom_iff_of_cylinder hY (cond α c k) (cond α k c)
  rw [Bool.apply_cond (DiagSet.Vertex.map ((π̃ false).app Y)),
    Bool.apply_cond (DiagSet.Vertex.map ((π̃ false).app Y)),
    Bool.apply_cond (DiagSet.Vertex.map ((π̃ true).app Y)),
    Bool.apply_cond (DiagSet.Vertex.map ((π̃ true).app Y)), hc₀, hc₁, hk, hk] at hcyl
  exact hcyl.1 ((hmap x).2 (h x))

private theorem exists_eq_simplexHom_δ (j : atomSimplex 0 ⟶ atomSimplex 1) :
    ∃ i : Fin 2, j = simplexHom (SimplexCategory.δ i).toOrderHom := by
  obtain ⟨j', rfl⟩ := simplexFunctor.map_surjective (X := ⦋0⦌) (Y := ⦋1⦌) j
  have : Mono j' :=
    SimplexCategory.mono_iff_injective.2 fun a b _ => Subsingleton.elim (α := Fin 1) a b
  obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono j'
  exact ⟨i, simplexFunctor_map _⟩

private theorem exists_reversibleCylinder_of_isEquivalence (hX : HasWeakComposites X)
    {t t' : X.Vertex} (e : SSet.Edge (X.vertexEquivSSet t) (X.vertexEquivSSet t'))
    (he : IsEquivalence X (e.edge : diagram X (atomSimplex 1))) :
    ∃ (c : (reversiblePathSpace.obj X).Vertex) (β : Bool),
      c.map ((π̃ β).app X) = t ∧
        c.map ((π̃ (!β)).app X) = t' := by
  have hW₁ : (grayCylinder.obj (atomSimplex 0)).dimension = 1 := by
    rw [dimension_grayCylinder_obj, dimension_atomSimplex]
  obtain ⟨θ⟩ := (nonempty_iso_atomGlobe_of_dimension_eq_one hW₁).map
    fun i => i.symm ≪≫ atomSimplexOneIsoGlobe.symm
  have hW : 0 < (grayCylinder.obj (atomSimplex 0)).dimension := by omega
  obtain ⟨h, hh⟩ := exists_reversibleCylinder_map.{u} hW hW₁ (Iso.refl _)
  obtain ⟨g, hg⟩ := (exists_toWalkingEquivalence_comp_eq_iff _ hW hX
    (X.map θ.hom.op (e.edge : diagram X (atomSimplex 1)))).2 ((isEquivalence_map_iso_iff θ _).2 he)
  let c : (reversiblePathSpace.obj X).Vertex :=
    uliftYonedaEquiv (X := atomSimplex 0) (F := reversiblePathSpace.obj X)
      (reversiblePathSpaceAdjunction.homEquiv _ _ (h ≫ g))
  have hend (ε : Bool) : c.map ((π̃ ε).app X) =
      (X.map ((grayEndpoint ε).app (atomSimplex 0) ≫ θ.hom).op
        (e.edge : diagram X (atomSimplex 1)) : X.Vertex) := by
    refine (uliftYonedaEquiv_comp (X := atomSimplex 0) (F := reversiblePathSpace.obj X) _
      ((π̃ ε).app X)).symm.trans ?_
    rw [reversibleCylinder.comp_pathEndpoint_app, Equiv.symm_apply_apply, ← Category.assoc, hh ε,
      Iso.refl_hom, Category.comp_id, Category.assoc, hg]
    refine (congrArg uliftYonedaEquiv (uliftYonedaEquiv_symm_map (F := X)
      ((grayEndpoint ε).app (atomSimplex 0)).op _).symm).trans
        ((Equiv.apply_symm_apply _ _).trans ?_)
    rw [op_comp]
    exact (Functor.map_comp_apply X _ _ _).symm
  have hne : (grayEndpoint false).app (atomSimplex 0) ≫ θ.hom ≠
      (grayEndpoint true).app (atomSimplex 0) ≫ θ.hom := fun hj => by
    have h₁ := ConcreteCategory.congr_hom (cancel_mono θ.hom |>.1 hj) (atomSimplex 0).top
    have h₂ := congrArg (fun z => ((cylAtomIso (atomSimplex 0)).inv z).1) h₁
    simp only [symm_grayEndpoint_apply] at h₂
    exact Bool.false_ne_true (SuspCarrier.pole.inj h₂)
  obtain ⟨i, hi⟩ := exists_eq_simplexHom_δ ((grayEndpoint false).app (atomSimplex 0) ≫ θ.hom)
  obtain ⟨i', hi'⟩ := exists_eq_simplexHom_δ ((grayEndpoint true).app (atomSimplex 0) ≫ θ.hom)
  have hs : X.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom).op
      (e.edge : diagram X (atomSimplex 1)) = (t : diagram X (atomSimplex 0)) := e.src_eq
  have ht : X.map (simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom).op
      (e.edge : diagram X (atomSimplex 1)) = (t' : diagram X (atomSimplex 0)) := e.tgt_eq
  refine ⟨c, ?_⟩
  fin_cases i <;> fin_cases i'
  · exact absurd (hi.trans hi'.symm) hne
  · exact ⟨true, by rw [hend, hi']; exact hs, by rw [Bool.not_true, hend, hi]; exact ht⟩
  · exact ⟨false, by rw [hend, hi]; exact hs, by rw [Bool.not_false, hend, hi']; exact ht⟩
  · exact absurd (hi.trans hi'.symm) hne

theorem DiagSet.hasContractibleHoms_iff_of_ends (hX : IsInftyCategory 1 X) (α β : Bool)
    (c : (reversiblePathSpace.obj X).Vertex) {a b : X.Vertex}
    (ha : c.map ((π̃ β).app X) = a)
    (hb : c.map ((π̃ (!β)).app X) = b) :
    X.HasContractibleHoms α a ↔ X.HasContractibleHoms α b := by
  refine forall_congr' fun x => ?_
  set k := x.map ((ν̃).app X)
  have hk (γ : Bool) : k.map ((π̃ γ).app X) = x := by
    have e : (ν̃).app X ≫ (π̃ γ).app X = 𝟙 X :=
      reversibleCylinder.pathConstant_app_comp_pathEndpoint_app _ γ X
    simp only [k, DiagSet.Vertex.map, ← NatTrans.comp_app_apply, e]
    rfl
  have H := DiagSet.isContractible_bipointedHom_iff_of_cylinder hX (cond α k c) (cond α c k)
  rw [Bool.apply_cond (DiagSet.Vertex.map ((π̃ false).app X)),
    Bool.apply_cond (DiagSet.Vertex.map ((π̃ false).app X)),
    Bool.apply_cond (DiagSet.Vertex.map ((π̃ true).app X)),
    Bool.apply_cond (DiagSet.Vertex.map ((π̃ true).app X)), hk, hk] at H
  cases β
  · rw [Bool.not_false] at hb
    rw [ha, hb] at H
    exact H
  · rw [Bool.not_true] at hb
    rw [ha, hb] at H
    exact H.symm

theorem DiagSet.hasContractibleHoms_iff_of_isEquivalence (hX : IsInftyCategory 1 X) (α : Bool)
    {t t' : X.Vertex} (e : X.Edge t t') (he : IsEquivalence X e.cell) :
    X.HasContractibleHoms α t ↔ X.HasContractibleHoms α t' := by
  obtain ⟨c, β, hc, hc'⟩ := exists_reversibleCylinder_of_isEquivalence hX.1 (X.edgeEquivSSet e)
    ((isEquivalence_map_iso_iff atomSimplexOneIsoGlobe e.cell).2 he)
  exact DiagSet.hasContractibleHoms_iff_of_ends hX α β c hc hc'

theorem DiagSet.exists_hasContractibleHoms_iff_map (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)]
    (y : Y.Vertex) :
    ∃ x : X.Vertex, ∀ α : Bool,
      Y.HasContractibleHoms α y ↔ Y.HasContractibleHoms α (x.map F) := by
  obtain ⟨x, c, hc₀, hc₁⟩ := exists_reversibleCylinder_of_weakEquivalence hX hY F y
  exact ⟨x, fun α => (DiagSet.hasContractibleHoms_iff_of_ends hY α false c hc₀ hc₁).symm⟩

noncomputable def DiagSet.isTerminalHomotopyCategoryOfIsFinal (hX : IsInftyCategory 1 X)
    {t : X.Vertex} (ht : SSet.IsFinal (X.vertexEquivSSet t)) :
    IsTerminal (⟨t⟩ : HomotopyCategory X hX.1) :=
  haveI : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj X ((isFibrant_infty_iff 1 X).2 hX)
  (SSet.isTerminalOfIsFinal ht).isTerminalObj (homotopyCategoryEquivalence hX).inverse

theorem DiagSet.IsContractible.rlp_monomorphisms {G : DiagSet.{u}}
    (hG : IsFibrant ((DiagSet.toInfty 0).obj G)) (h : G.IsContractible) :
    (monomorphisms DiagSet.{u}).rlp (isTerminalBallAtomPoint.from G) := by
  have : Fibration ((DiagSet.toInfty 0).map (isTerminalBallAtomPoint.from G)) :=
    (isFibrant_iff_of_isTerminal ((DiagSet.toInfty 0).map (isTerminalBallAtomPoint.from G))
      (isTerminalBallAtomPoint : IsTerminal ((DiagSet.toInfty 0).obj (ball atomPoint)))).1 hG
  have : WeakEquivalence ((DiagSet.toInfty 0).map (isTerminalBallAtomPoint.from G)) := h
  exact rlp_monomorphisms_of_trivialFibration_toInfty_map 0

theorem DiagSet.IsContractible.nonempty_vertex {G : DiagSet.{u}}
    (hG : IsFibrant ((DiagSet.toInfty 0).obj G)) (h : G.IsContractible) :
    Nonempty (G.Vertex) :=
  ⟨(exists_app_eq_of_rlp_monomorphisms (h.rlp_monomorphisms hG)
    (uliftYonedaEquiv (X := atomSimplex 0) (F := ball atomPoint)
      (isTerminalBallAtomPoint.from _))).choose⟩

theorem DiagSet.IsContractible.nonempty_edge {G : DiagSet.{u}}
    (hG : IsFibrant ((DiagSet.toInfty 0).obj G)) (h : G.IsContractible)
    (a b : G.Vertex) : Nonempty (G.Edge a b) := by
  have hGc : IsInftyCategory 0 G := (isFibrant_infty_iff 0 G).1 hG
  have := h.rlp_monomorphisms hG (reversibleCylinder.endpoints (ball.{u} atomPoint))
    (monomorphisms.infer_property _)
  have sq : CommSq (coprod.desc (vertexHom a) (vertexHom b))
      (reversibleCylinder.endpoints (ball.{u} atomPoint)) (isTerminalBallAtomPoint.from G)
      (isTerminalBallAtomPoint.from _) := ⟨isTerminalBallAtomPoint.hom_ext _ _⟩
  let g := reversiblePathSpaceAdjunction.homEquiv _ _ sq.lift
  have hg (α : Bool) : g ≫ (π̃ α).app G = vertexHom (cond α b a) := by
    rw [reversibleCylinder.comp_pathEndpoint_app, Equiv.symm_apply_apply]
    cases α
    · rw [← reversibleCylinder.inl_endpoints, Category.assoc, sq.fac_left, coprod.inl_desc]
      rfl
    · rw [← reversibleCylinder.inr_endpoints, Category.assoc, sq.fac_left, coprod.inr_desc]
      rfl
  let g' := vertexHom a ≫ (ν̃).app G
  have hg' (α : Bool) : g' ≫ (π̃ α).app G = vertexHom a := by
    rw [Category.assoc, reversibleCylinder.pathConstant_app_comp_pathEndpoint_app,
      Category.comp_id]
  have hend {k : ball.{u} atomPoint ⟶ reversiblePathSpace.obj G} {α : Bool}
      {v : G.Vertex} (hk : k ≫ (π̃ α).app G = vertexHom v) :
      ((π̃ α).app G).app _ (uliftYonedaEquiv k) = (v : diagram G (atomSimplex 0)) :=
    (uliftYonedaEquiv_comp (F := reversiblePathSpace.obj G) k _).symm.trans
      (by rw [hk, uliftYonedaEquiv_vertexHom])
  have hba := equivalent_reversiblePathEndpoint_of_equivalent 0 hGc
    (g := uliftYonedaEquiv g) (g' := uliftYonedaEquiv g')
    ⟨rfl, Or.inl (dimension_atomSimplex 0)⟩ false
    (by rw [hend (hg false), hend (hg' false)]; exact equivalent_refl _)
  rw [hend (hg (!false)), hend (hg' (!false))] at hba
  exact (DiagSet.nonempty_edge_iff_equivalent hGc a b).2 (equivalent_symm hba)

private theorem forall_exists_sphereInclusion_comp_eq_iff (p : Under pointPair.{u}) (U : Atom) :
    (∀ a : sphere.{u} U ⟶ bipointedHom.obj p, ∃ l, sphereInclusion U ≫ l = a) ↔
      ∀ b : Under.mk (sphereSuspensionPoles.{u} U) ⟶ p,
        ∃ c : suspendedBall.obj U ⟶ p, Under.homMk (V := suspendedBall.obj U)
          (sphereInclusion (atomSuspension.obj U)) (sphereSuspensionPoles_comp U) ≫ c = b := by
  have hsq := bipointedSuspension_map_sphereInclusion.{u} U
  have hi : Under.homMk (V := suspendedBall.obj U) (sphereInclusion (atomSuspension.obj U))
      (sphereSuspensionPoles_comp U) = (bipointedSuspensionSphereIso U).inv ≫
        bipointedSuspension.map (sphereInclusion U) ≫ (bipointedSuspensionBallIso U).hom := by
    rw [hsq, Iso.inv_hom_id_assoc]
  constructor
  · intro h b
    obtain ⟨l, hl⟩ := h (bipointedSuspensionAdjunction.homEquiv _ _
      ((bipointedSuspensionSphereIso U).hom ≫ b))
    refine ⟨(bipointedSuspensionBallIso U).inv ≫
      (bipointedSuspensionAdjunction.homEquiv _ _).symm l, ?_⟩
    rw [hi, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      ← Adjunction.homEquiv_naturality_left_symm, hl, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
  · intro h a
    obtain ⟨c, hc⟩ := h ((bipointedSuspensionSphereIso U).inv ≫
      (bipointedSuspensionAdjunction.homEquiv _ _).symm a)
    refine ⟨bipointedSuspensionAdjunction.homEquiv _ _ ((bipointedSuspensionBallIso U).hom ≫ c),
      ?_⟩
    rw [← Adjunction.homEquiv_naturality_left, ← Category.assoc, hsq, Category.assoc, hc,
      Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]

private theorem isContractible_iff_forall_exists {G : DiagSet.{u}}
    (hG : IsFibrant ((DiagSet.toInfty 0).obj G)) :
    G.IsContractible ↔ ∀ (U : Atom) (a : sphere.{u} U ⟶ G), ∃ l, sphereInclusion U ≫ l = a := by
  constructor
  · intro h U a
    have := h.rlp_monomorphisms hG (sphereInclusion U) (monomorphisms.infer_property _)
    have sq : CommSq a (sphereInclusion U) (isTerminalBallAtomPoint.from G)
        (isTerminalBallAtomPoint.from _) := ⟨isTerminalBallAtomPoint.hom_ext _ _⟩
    exact ⟨sq.lift, sq.fac_left⟩
  · intro h
    refine weakEquivalence_toInfty_map_of_rlp_monomorphisms 0 ?_
    rw [monomorphisms_eq_saturation_sphereInclusions, MorphismProperty.rlp_saturation]
    rintro _ _ _ ⟨U⟩
    refine ⟨fun {a _} _ => ?_⟩
    obtain ⟨l, hl⟩ := h U a
    exact ⟨⟨{ l := l, fac_left := hl, fac_right := isTerminalBallAtomPoint.hom_ext _ _ }⟩⟩

theorem DiagSet.hasContractibleHoms_iff_extend_sphere (hX : IsInftyCategory 1 X) (α : Bool)
    (t : X.Vertex) : X.HasContractibleHoms α t ↔ ∀ (x) (U : Atom)
      (b : Under.mk (sphereSuspensionPoles.{u} U) ⟶ X.bipoint (cond α x t) (cond α t x)),
        ∃ c : suspendedBall.obj U ⟶ X.bipoint (cond α x t) (cond α t x),
          Under.homMk (V := suspendedBall.obj U) (sphereInclusion (atomSuspension.obj U))
            (sphereSuspensionPoles_comp U) ≫ c = b :=
  forall_congr' fun _ => (isContractible_iff_forall_exists (isFibrant_bipointedHom hX)).trans
    (forall_congr' fun U => forall_exists_sphereInclusion_comp_eq_iff _ U)

@[instance_reducible]
private noncomputable def uniqueHomOfHasContractibleHoms (hX : IsInftyCategory 1 X) {α : Bool}
    {t : X.Vertex} (ht : X.HasContractibleHoms α t)
    (x : X.Vertex) :
    Unique ((⟨cond α x t⟩ : HomotopyCategory X hX.1) ⟶ ⟨cond α t x⟩) :=
  have hG : IsFibrant ((DiagSet.toInfty 0).obj
      (bipointedHom.obj (X.bipoint (cond α x t) (cond α t x)))) :=
    isFibrant_bipointedHom hX
  have hne := (ht x).nonempty_vertex hG
  have hsub : Subsingleton (SSet.π₀ (DiagSet.toSSet.obj
      (bipointedHom.obj (X.bipoint (cond α x t) (cond α t x))))) := ⟨fun a b => by
    induction a with | mk v => ?_
    induction b with | mk w => ?_
    obtain ⟨e⟩ := (ht x).nonempty_edge hG ((DiagSet.vertexEquivSSet _).symm v)
      ((DiagSet.vertexEquivSSet _).symm w)
    exact SSet.π₀.sound (DiagSet.edgeEquivSSet e)⟩
  @uniqueOfSubsingleton _
    ((X.bipointedHomπ₀Equiv hX (cond α x t) (cond α t x)).symm.subsingleton)
    (X.bipointedHomπ₀Equiv hX _ _ (SSet.π₀.mk hne.some))

noncomputable def DiagSet.isTerminalOfIsFinalObject (hX : IsInftyCategory 1 X)
    {t : X.Vertex} (ht : X.IsFinalObject t) :
    IsTerminal (⟨t⟩ : HomotopyCategory X hX.1) :=
  IsTerminal.ofUniqueHom (fun x => (uniqueHomOfHasContractibleHoms hX ht x.pt).default)
    fun x _ => (uniqueHomOfHasContractibleHoms hX ht x.pt).uniq _

noncomputable def DiagSet.isInitialOfIsInitialObject (hX : IsInftyCategory 1 X)
    {t : X.Vertex} (ht : X.IsInitialObject t) :
    IsInitial (⟨t⟩ : HomotopyCategory X hX.1) :=
  IsInitial.ofUniqueHom (fun x => (uniqueHomOfHasContractibleHoms hX ht x.pt).default)
    fun x _ => (uniqueHomOfHasContractibleHoms hX ht x.pt).uniq _

theorem DiagSet.isZero_of_isZeroObject (hX : IsInftyCategory 1 X)
    {t : X.Vertex} (ht : X.IsZeroObject t) :
    IsZero (⟨t⟩ : HomotopyCategory X hX.1) :=
  ⟨fun x => ⟨uniqueHomOfHasContractibleHoms hX (ht false) x.pt⟩,
    fun x => ⟨uniqueHomOfHasContractibleHoms hX (ht true) x.pt⟩⟩

theorem DiagSet.isEquivalence_of_hasContractibleHoms (hX : IsInftyCategory 1 X) (α : Bool)
    {t t' : X.Vertex} (ht : X.HasContractibleHoms α t)
    (ht' : X.HasContractibleHoms α t') (e : X.Edge t t') : IsEquivalence X e.cell := by
  rw [← HomotopyCategory.isIso_homMk_iff]
  cases α
  · exact isIso_of_isInitial (X.isInitialOfIsInitialObject hX ht)
      (X.isInitialOfIsInitialObject hX ht') _
  · exact isIso_of_isTerminal (X.isTerminalOfIsFinalObject hX ht)
      (X.isTerminalOfIsFinalObject hX ht') _

theorem DiagSet.nonempty_edge_of_hasContractibleHoms (hX : IsInftyCategory 1 X) (α : Bool)
    {t t' : X.Vertex} (ht : X.HasContractibleHoms α t)
    (ht' : X.HasContractibleHoms α t') : Nonempty (X.Edge t t') := by
  cases α
  · exact ⟨(HomotopyCategory.homMk_surjective hX.1
      (uniqueHomOfHasContractibleHoms hX ht t').default).choose⟩
  · exact ⟨(HomotopyCategory.homMk_surjective hX.1
      (uniqueHomOfHasContractibleHoms hX ht' t).default).choose⟩

end Atoms.Diagrammatic
