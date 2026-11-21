import Atoms.Diagrammatic.Vertex
import Atoms.Diagrammatic.Marked.Above
import Atoms.Diagrammatic.Marked.FlatEquivalence
import Atoms.Diagrammatic.SimplicialAdjunction
import Atoms.Homotopical.Simplicial.Joyal
import Atoms.Shape.SimplexFace

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

noncomputable def _root_.SSet.toDiagSetInfty : SSet.{u} ⥤ DiagSet.Infty 1 := SSet.toDiagSet

def DiagSet.Infty.toSSet : DiagSet.Infty.{u} 1 ⥤ SSet.{u} := DiagSet.toSSet

noncomputable def DiagSet.Infty.sSetDiagSetAdj : SSet.toDiagSetInfty ⊣ DiagSet.Infty.toSSet.{u} :=
  Atoms.Diagrammatic.sSetDiagSetAdj

noncomputable def flatToMarkedAbove (n : ℕ) (X : DiagSet.{u}) :
    (MarkedPresheaf.flat atomMarking).obj X ⟶ (MarkedDiagSet.markedAboveFunctor n).obj X :=
  MarkedPresheaf.homMk (Y := MarkedDiagSet.markedAbove X n) (𝟙 X) fun V _ hx =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (Or.inl ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V _).1 hx))

theorem weakEquivalence_flatToMarkedAbove (n : ℕ) (X : DiagSet.{u}) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (flatToMarkedAbove n X)) := by
  have : IsIso (MarkedPresheaf.forget.map (flatToMarkedAbove n X)) :=
    inferInstanceAs (IsIso (𝟙 X))
  refine weakEquivalence_of_isIso_forget_map n _ fun Z hZ g hA U x hx => ?_
  rcases (MarkedPresheaf.mem_marked_ofMarking _ _ U _).1 hx with hd | hd
  · exact hA U x ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ U _).2 hd)
  · exact hZ.2 U _ (Nat.cast_lt.2 hd)

theorem weakEquivalence_of_weakEquivalence_markedAboveFunctor_map (n : ℕ) {X Y : DiagSet.{u}}
    (f : X ⟶ Y)
    (h : WeakEquivalence ((MarkedDiagSet.Coinductive.markedAboveFunctor n).map f)) :
    WeakEquivalence ((DiagSet.toInfty n).map f) := by
  refine (weakEquivalence_flat_map_iff n _).1 ?_
  have e : (MarkedPresheaf.flat atomMarking).map f ≫ flatToMarkedAbove n Y =
      flatToMarkedAbove n X ≫ (MarkedDiagSet.markedAboveFunctor n).map f :=
    MarkedPresheaf.hom_ext rfl
  have hX := (weakEquivalence_iff _).1 (weakEquivalence_flatToMarkedAbove n X)
  have hY := weakEquivalence_flatToMarkedAbove n Y
  exact (weakEquivalence_iff _).2 ((weakEquivalences _).of_postcomp _ _
    ((weakEquivalence_iff _).1 hY)
    ((congrArg (fun g => weakEquivalences (MarkedDiagSet.Coinductive n) g) e).mpr
      ((weakEquivalences _).comp_mem _ _ hX ((weakEquivalence_iff _).1 h))))

section SimplexHorn

open Atoms.Molecule Atoms.Molecule.OGP Simplicial Opposite

theorem homEquiv_app_mem_horn (m : ℕ) (k : Fin (m + 2)) (d : SimplexCategoryᵒᵖ)
    (σ : (Λ[m + 1, k] : SSet.{u}).obj d) :
    (sSetDiagSetAdj.homEquiv _ _ (toDiagSetObjStdSimplexIso (m + 1)).hom).app d σ.1 ∈
      (closedSubpresheaf (simplexHornData m k).atom
        (hornSubset (simplexHornData m k).toHornData)).obj (op (atomSimplex d.unop.len)) := by
  rw [homEquiv_toDiagSetObjStdSimplexIso_hom_app]
  intro t
  obtain ⟨j, hjk, hj⟩ := (SSet.mem_horn_iff_notMem_range (n := m + 1) (d := d.unop.len) σ.1 k).1
    σ.2
  refine (mem_hornSubset_simplexHornData_iff m k _).2 ⟨j, hjk, fun hj' => hj ?_⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ((congrArg (j ∈ ·) (atomSimplexVertices_simplexHom
    (SimplexCategory.Hom.toOrderHom (SSet.stdSimplex.objEquiv σ.1)) t)).mp hj')
  exact ⟨i, rfl⟩

noncomputable def toDiagSetHornToHorn (m : ℕ) (k : Fin (m + 2)) :
    SSet.toDiagSet.obj (Λ[m + 1, k] : SSet.{u}) ⟶ horn (simplexHornData m k).toHornData :=
  (sSetDiagSetAdj.homEquiv _ _).symm
    { app d := ↾fun σ => ⟨_, homEquiv_app_mem_horn m k d σ⟩
      naturality d d' f := by
        ext σ
        refine Subtype.ext ?_
        exact NatTrans.naturality_apply
          (sSetDiagSetAdj.homEquiv _ _ (toDiagSetObjStdSimplexIso (m + 1)).hom) f σ.1 }

theorem toDiagSetHornToHorn_comp_hornInclusion (m : ℕ) (k : Fin (m + 2)) :
    toDiagSetHornToHorn.{u} m k ≫ hornInclusion (simplexHornData m k).toHornData =
      SSet.toDiagSet.map Λ[m + 1, k].ι ≫ (toDiagSetObjStdSimplexIso (m + 1)).hom := by
  refine (sSetDiagSetAdj.homEquiv _ _).injective ?_
  refine (sSetDiagSetAdj.homEquiv_naturality_right _ _).trans
    (Eq.trans ?_ (sSetDiagSetAdj.homEquiv_naturality_left _ _).symm)
  rw [toDiagSetHornToHorn, Equiv.apply_symm_apply]
  rfl

theorem exists_toDiagSetHornToHorn_app_eq (m : ℕ) (k : Fin (m + 2)) (U : Atomᵒᵖ)
    (y : (horn.{u} (simplexHornData m k).toHornData).obj U) :
    ∃ (j : Fin (m + 2)) (hjk : j ≠ k) (z : (SSet.toDiagSet.obj Δ[m]).obj U),
      (toDiagSetHornToHorn m k).app U ((SSet.toDiagSet.map (SSet.horn.ι k j hjk)).app U z) =
        y ∧ ((toDiagSetObjStdSimplexIso m).hom.app U z).down ≫
          simplexHom (SimplexCategory.δ j).toOrderHom = y.1.down := by
  obtain ⟨j, hjk, hj⟩ := (mem_hornSubset_simplexHornData_iff m k _).1 (y.2 U.unop.top)
  obtain ⟨g, hg⟩ := (exists_comp_simplexHom_eq_iff (e := (SimplexCategory.δ j).toOrderHom)
    (SimplexCategory.mono_iff_injective.1 inferInstance) y.1.down).2 (by
      rw [show Finset.univ.image (SimplexCategory.δ j).toOrderHom = {j}ᶜ from
        Fin.image_succAbove_univ j]
      intro i hi
      rw [Finset.mem_compl, Finset.mem_singleton]
      rintro rfl
      exact hj hi)
  obtain ⟨z, hz⟩ := (epi_iff_surjective ((toDiagSetObjStdSimplexIso m).hom.app U)).1
    inferInstance ⟨g⟩
  have hzy : ((toDiagSetObjStdSimplexIso m).hom.app U z).down ≫
      simplexHom (SimplexCategory.δ j).toOrderHom = y.1.down := by
    rw [hz]
    exact hg
  refine ⟨j, hjk, z, Subtype.ext ?_, hzy⟩
  have h₁ := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toDiagSetHornToHorn_comp_hornInclusion m k) U)
    ((SSet.toDiagSet.map (SSet.horn.ι k j hjk)).app U z)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₁
  have h₂ : SSet.toDiagSet.map (SSet.horn.ι k j hjk) ≫ SSet.toDiagSet.map Λ[m + 1, k].ι ≫
      (toDiagSetObjStdSimplexIso (m + 1)).hom =
        SSet.toDiagSet.map (SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
          (toDiagSetObjStdSimplexIso (m + 1)).hom :=
    (Functor.map_comp_assoc _ _ _ _).symm.trans
      (congrArg (fun f => SSet.toDiagSet.map f ≫ (toDiagSetObjStdSimplexIso (m + 1)).hom)
        (SSet.horn.ι_ι k j hjk))
  exact h₁.trans ((ConcreteCategory.congr_hom (NatTrans.congr_app h₂ U) z).trans
    ((toDiagSetObjStdSimplexIso_hom_app_map (SimplexCategory.δ j) U z).trans
      (congrArg ULift.up hzy)))

instance isIso_toDiagSetHornToHorn (m : ℕ) (k : Fin (m + 2)) :
    IsIso (toDiagSetHornToHorn.{u} m k) := by
  have h₀ : Mono (SSet.toDiagSet.map Λ[m + 1, k].ι) := SSet.toDiagSet.map_mono _
  have hmono : Mono (toDiagSetHornToHorn m k) :=
    @mono_of_mono_fac _ _ _ _ _ _ _ _ (@mono_comp _ _ _ _ _ _ h₀ _
      (IsIso.mono_of_iso (toDiagSetObjStdSimplexIso (m + 1)).hom))
      (toDiagSetHornToHorn_comp_hornInclusion m k)
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [CategoryTheory.isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hmono U), fun y => ?_⟩
  obtain ⟨j, hjk, z, hz, -⟩ := exists_toDiagSetHornToHorn_app_eq m k U y
  exact ⟨_, hz⟩

noncomputable def toDiagSetHornArrowIso (m : ℕ) (k : Fin (m + 2)) :
    Arrow.mk (SSet.toDiagSet.map Λ[m + 1, k].ι) ≅
      Arrow.mk (hornInclusion.{u} (simplexHornData m k).toHornData) :=
  Arrow.isoMk (asIso (toDiagSetHornToHorn m k)) (toDiagSetObjStdSimplexIso (m + 1))
    (toDiagSetHornToHorn_comp_hornInclusion m k)

theorem weakEquivalence_toDiagSet_map_horn_ι (m : ℕ) (k : Fin (m + 2)) (h0 : k ≠ 0)
    (hl : k ≠ Fin.last (m + 1)) :
    WeakEquivalence (SSet.toDiagSetInfty.{u}.map Λ[m + 1, k].ι) := by
  refine weakEquivalence_of_weakEquivalence_markedAboveFunctor_map 1 (SSet.toDiagSet.map _) ?_
  obtain ⟨m', ⟨E⟩⟩ := exists_markedHornData_iso_markedAbove_hornInclusion (simplexHornData m k)
    (simplexFacet m k) rfl (boundary_closure_simplexFacet_zero m k h0 hl)
  have hm : markedExactCylinder.{u}.weakEquivalences (coinductiveGenerators 1)
      (markedHornInclusion m') :=
    markedExactCylinder.{u}.anodyne_le_weakEquivalences _ (coinductiveGenerators_le_monomorphisms 1)
      _ (markedExactCylinder.{u}.le_anodyne _ _ (by
        unfold coinductiveGenerators
        exact (le_sup_left.trans le_sup_left : markedHorns ≤ _) _ (MorphismProperty.ofHoms.mk m')))
  have E' := (MarkedDiagSet.markedAboveFunctor 1).mapArrow.mapIso
    (toDiagSetHornArrowIso m k)
  have := MorphismProperty.respectsIso_of_isStableUnderComposition
    (markedExactCylinder.{u}.isomorphisms_le_weakEquivalences (coinductiveGenerators (1 : ℕ∞)))
  exact (weakEquivalence_iff _).2
    (((markedExactCylinder.{u}.weakEquivalences _).arrow_mk_iso_iff E').2
      (((markedExactCylinder.{u}.weakEquivalences _).arrow_mk_iso_iff E).1 hm))

end SimplexHorn

open Simplicial

theorem innerFibration_toSSet_map {X Y : DiagSet.Infty.{u} 1} (p : X ⟶ Y) (hp : Fibration p) :
    SSet.InnerFibration (DiagSet.Infty.toSSet.map p) := by
  rw [SSet.innerFibration_iff]
  rintro _ _ _ ⟨i, h0, hn⟩
  rw [← DiagSet.Infty.sSetDiagSetAdj.hasLiftingProperty_iff]
  have := weakEquivalence_toDiagSet_map_horn_ι _ i (ne_of_gt h0) (ne_of_lt hn)
  have : Cofibration (SSet.toDiagSetInfty.map Λ[_ + 2, i].ι) :=
    (cofibration_iff _).2 (SSet.toDiagSet.map_mono _)
  infer_instance

theorem quasicategory_toSSet_obj (X : DiagSet.Infty.{u} 1) (hX : IsFibrant X) :
    (DiagSet.Infty.toSSet.obj X).Quasicategory := by
  have hI : SSet.InnerFibration (DiagSet.Infty.toSSet.map (terminal.from X)) :=
    innerFibration_toSSet_map _ ((isFibrant_iff X).1 hX)
  have : PreservesLimitsOfSize.{u, u} DiagSet.Infty.toSSet :=
    DiagSet.Infty.sSetDiagSetAdj.rightAdjoint_preservesLimits
  exact (SSet.quasicategory_iff_of_isTerminal _
    (terminalIsTerminal.isTerminalObj DiagSet.Infty.toSSet _)).2 hI

section Edges

open Atoms.Molecule Atoms.Molecule.OGP Simplicial Opposite

theorem isEquivalence_map_of_dimension_pos {X : DiagSet.{u}} {e : diagram X (atomSimplex 1)}
    (he : IsEquivalence X e) {V : Atom} (hV : 0 < V.dimension) (g : V ⟶ atomSimplex 1) :
    IsEquivalence X (X.map g.op e) := by
  by_cases hv : g V.top = (atomSimplex 1).top
  · by_cases hiso : IsIso g
    · exact (isEquivalence_map_iso_iff (asIso g) e).2 he
    · exact degenerate_isEquivalence X _ ⟨_, g, e, isCollapseHom_of_apply_eq_top g hv, hiso, rfl⟩
  · have htop : grade ℕ (atomSimplex 1).top = 1 := by
      have := card_atomSimplexVertices (atomSimplex 1).top
      rw [atomSimplexVertices_top, Finset.card_univ, Fintype.card_fin] at this
      omega
    have hd : grade ℕ (g V.top) = 0 := by
      have := grade_strictMono (𝕆 := ℕ) (lt_of_le_of_ne ((atomSimplex 1).le_top _) hv)
      omega
    let p := principalLift (atomSimplex 1) (g V.top) g (apply_mem_closure_apply_top g)
    have hp : IsCollapseHom p := isCollapseHom_of_apply_eq_top _ (principalLift_apply_top g)
    have hni : ¬IsIso p := fun h => by
      have := Atom.dimension_eq_of_iso (asIso p)
      rw [Atom.dimension_ofClosure, hd] at this
      omega
    refine degenerate_isEquivalence X _ ⟨_, p, X.map (Atom.closureIncl _ _).op e, hp, hni, ?_⟩
    exact (Functor.map_comp_apply X (Atom.closureIncl _ _).op p.op e).symm.trans
      (congrArg (fun f : V ⟶ atomSimplex 1 => X.map f.op e)
        (principalLift_comp_closureIncl _ _ g (apply_mem_closure_apply_top g)))

theorem exists_hornInclusion_comp_eq {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) (H : HornData)
    (hH : ∃ m : MarkedHornData, m.toHornData = H) (q : horn H ⟶ X)
    (hq : ∀ (V : Atom) (c : (horn H).obj (op V)), 0 < V.dimension →
      IsEquivalence X (q.app _ c)) :
    ∃ r : ball H.atom ⟶ X, hornInclusion H ≫ r = q := by
  obtain ⟨m, rfl⟩ := hH
  have hR := (isFibrant_coinductive_iff 1 _).1 (isFibrant_coinductive_natural 1 hX)
  have hM : HasMarkedRLP markedHorns (MarkedDiagSet.natural.obj X) :=
    ((hasMarkedRLP_sup _ _ _).1 ((hasMarkedRLP_sup _ _ _).1 hR).1).1
  let q' : m.source ⟶ MarkedDiagSet.natural.obj X :=
    MarkedPresheaf.homMk (X := m.source) q fun V c hc =>
      (MarkedDiagSet.mem_marked_natural_iff X V _).2 (hq V c hc.1)
  obtain ⟨f, hf⟩ := hasMarkedRLP_iff.1 hM _ (MorphismProperty.ofHoms.mk m) q'
  refine ⟨(closedSubpresheafUnivIso m.atom).inv ≫ MarkedPresheaf.forget.map f, ?_⟩
  exact ((Functor.map_comp _ _ _).symm.trans (congrArg MarkedPresheaf.forget.map hf) :)

theorem exists_horn_two_ι_comp_eq {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) (k : Fin 3)
    (τ : (Λ[2, k] : SSet.{u}) ⟶ DiagSet.toSSet.obj X)
    (hτ : ∀ (j : Fin 3) (hjk : j ≠ k), IsEquivalence X
      (SSet.yonedaEquiv (SSet.horn.ι k j hjk ≫ τ) : diagram X (atomSimplex 1))) :
    ∃ σ : Δ[2] ⟶ DiagSet.toSSet.obj X, Λ[2, k].ι ≫ σ = τ := by
  let q := inv (toDiagSetHornToHorn 1 k) ≫ (sSetDiagSetAdj.homEquiv _ _).symm τ
  have hq : ∀ (V : Atom) (c : (horn (simplexHornData 1 k).toHornData).obj (op V)),
      0 < V.dimension → IsEquivalence X (q.app _ c) := by
    intro V c hV
    obtain ⟨j, hjk, z, hz, -⟩ := exists_toDiagSetHornToHorn_app_eq 1 k (op V) c
    have h₁ : q.app (op V) c = ((sSetDiagSetAdj.homEquiv _ _).symm τ).app (op V)
        ((SSet.toDiagSet.map (SSet.horn.ι k j hjk)).app (op V) z) := by
      rw [← hz]
      exact ConcreteCategory.congr_hom (NatTrans.congr_app
        (IsIso.hom_inv_id_assoc (toDiagSetHornToHorn 1 k)
          ((sSetDiagSetAdj.homEquiv _ _).symm τ)) (op V)) _
    have h₂ := ConcreteCategory.congr_hom (NatTrans.congr_app
      (sSetDiagSetAdj.homEquiv_naturality_left_symm (SSet.horn.ι k j hjk) τ) (op V)) z
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₂
    have h₃ := ConcreteCategory.congr_hom (NatTrans.congr_app
      (homEquiv_symm_yonedaEquiv_symm (SSet.yonedaEquiv (SSet.horn.ι k j hjk ≫ τ))) (op V)) z
    rw [Equiv.symm_apply_apply] at h₃
    exact (congrArg (IsEquivalence X) (h₁.trans (h₂.symm.trans h₃))).mpr
      (isEquivalence_map_of_dimension_pos (hτ j hjk) hV
        ((toDiagSetObjStdSimplexIso 1).hom.app (op V) z).down)
  obtain ⟨r, hr⟩ := exists_hornInclusion_comp_eq hX _
    (AtomicHornData.exists_markedHornData (simplexHornData 1 k)) q hq
  refine ⟨sSetDiagSetAdj.homEquiv _ _ ((toDiagSetObjStdSimplexIso 2).hom ≫ r), ?_⟩
  refine (sSetDiagSetAdj.homEquiv_naturality_left _ _).symm.trans ?_
  refine (congrArg (sSetDiagSetAdj.homEquiv _ _) ?_).trans
    ((sSetDiagSetAdj.homEquiv _ _).apply_symm_apply τ)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r)
    (toDiagSetHornToHorn_comp_hornInclusion 1 k).symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) hr).trans (IsIso.hom_inv_id_assoc _ _))))

theorem exists_compStruct_of_isEquivalence_horn_zero {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {x₀ x₁ x₂ : (DiagSet.toSSet.obj X) _⦋0⦌} (e₀₁ : SSet.Edge x₀ x₁)
    (e₀₂ : SSet.Edge x₀ x₂) (h₀₁ : IsEquivalence X (e₀₁.edge : diagram X (atomSimplex 1)))
    (h₀₂ : IsEquivalence X (e₀₂.edge : diagram X (atomSimplex 1))) :
    ∃ e₁₂ : SSet.Edge x₁ x₂, Nonempty (SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  let a : ∀ j : Fin 3, j ≠ 0 → (Δ[1] ⟶ DiagSet.toSSet.obj X) := fun j _ =>
    SSet.yonedaEquiv.symm (if j = 1 then e₀₂.edge else e₀₁.edge)
  have ha : SSet.horn.IsCompatible a := by
    rw [SSet.horn.isCompatible_iff]
    intro j k hj hk hjk
    have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hjk' : j.val < k.val := hjk
    have hk' := k.isLt
    obtain rfl : j = 1 := Fin.ext (by change j.val = 1; omega)
    obtain rfl : k = 2 := Fin.ext (by change k.val = 2; omega)
    refine (SSet.stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans
      (Eq.trans ?_ (SSet.stdSimplex.δ_comp_yonedaEquiv_symm _ _).symm)
    exact congrArg SSet.yonedaEquiv.symm (e₀₂.src_eq.trans e₀₁.src_eq.symm)
  have hτ : ∀ (j : Fin 3) (hj : j ≠ 0), SSet.yonedaEquiv (SSet.horn.ι 0 j hj ≫ ha.desc) =
      if j = 1 then e₀₂.edge else e₀₁.edge := fun j hj => by
    rw [SSet.horn.IsCompatible.ι_desc, Equiv.apply_symm_apply]
  obtain ⟨σ, hσ⟩ := exists_horn_two_ι_comp_eq hX 0 ha.desc fun j hj => by
    rw [hτ j hj]
    split_ifs
    exacts [h₀₂, h₀₁]
  have hface : ∀ (j : Fin 3) (hj : j ≠ 0), (DiagSet.toSSet.obj X).δ j
      (SSet.yonedaEquiv σ) = if j = 1 then e₀₂.edge else e₀₁.edge := fun j hj =>
    (SSet.stdSimplex.yonedaEquiv_δ_comp σ j).symm.trans
      ((congrArg (fun f => SSet.yonedaEquiv (f ≫ σ)) (SSet.horn.ι_ι 0 j hj).symm).trans
        ((congrArg (fun f => SSet.yonedaEquiv (SSet.horn.ι 0 j hj ≫ f)) hσ).trans (hτ j hj)))
  obtain ⟨y₀, y₁, y₂, f₀₁, f₁₂, f₀₂, h, hs⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv σ)
  have h₂ : f₀₁.edge = e₀₁.edge := h.d₂.symm.trans (hs ▸ hface 2 (by decide))
  have h₁ : f₀₂.edge = e₀₂.edge := h.d₁.symm.trans (hs ▸ hface 1 (by decide))
  obtain rfl : y₀ = x₀ := f₀₁.src_eq.symm.trans ((congrArg _ h₂).trans e₀₁.src_eq)
  obtain rfl : y₁ = x₁ := f₀₁.tgt_eq.symm.trans ((congrArg _ h₂).trans e₀₁.tgt_eq)
  obtain rfl : y₂ = x₂ := f₀₂.tgt_eq.symm.trans ((congrArg _ h₁).trans e₀₂.tgt_eq)
  obtain rfl : f₀₁ = e₀₁ := SSet.Edge.ext h₂
  obtain rfl : f₀₂ = e₀₂ := SSet.Edge.ext h₁
  exact ⟨f₁₂, ⟨h⟩⟩

theorem exists_compStruct_of_isEquivalence_horn_two {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {x₀ x₁ x₂ : (DiagSet.toSSet.obj X) _⦋0⦌} (e₁₂ : SSet.Edge x₁ x₂)
    (e₀₂ : SSet.Edge x₀ x₂) (h₁₂ : IsEquivalence X (e₁₂.edge : diagram X (atomSimplex 1)))
    (h₀₂ : IsEquivalence X (e₀₂.edge : diagram X (atomSimplex 1))) :
    ∃ e₀₁ : SSet.Edge x₀ x₁, Nonempty (SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  let a : ∀ j : Fin 3, j ≠ 2 → (Δ[1] ⟶ DiagSet.toSSet.obj X) := fun j _ =>
    SSet.yonedaEquiv.symm (if j = 0 then e₁₂.edge else e₀₂.edge)
  have ha : SSet.horn.IsCompatible a := by
    rw [SSet.horn.isCompatible_iff]
    intro j k hj hk hjk
    have hk' : k.val ≠ 2 := fun h => hk (Fin.ext h)
    have hjk' : j.val < k.val := hjk
    have hk'' := k.isLt
    obtain rfl : j = 0 := Fin.ext (by change j.val = 0; omega)
    obtain rfl : k = 1 := Fin.ext (by change k.val = 1; omega)
    refine (SSet.stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans
      (Eq.trans ?_ (SSet.stdSimplex.δ_comp_yonedaEquiv_symm _ _).symm)
    exact congrArg SSet.yonedaEquiv.symm (e₁₂.tgt_eq.trans e₀₂.tgt_eq.symm)
  have hτ : ∀ (j : Fin 3) (hj : j ≠ 2), SSet.yonedaEquiv (SSet.horn.ι 2 j hj ≫ ha.desc) =
      if j = 0 then e₁₂.edge else e₀₂.edge := fun j hj => by
    rw [SSet.horn.IsCompatible.ι_desc, Equiv.apply_symm_apply]
  obtain ⟨σ, hσ⟩ := exists_horn_two_ι_comp_eq hX 2 ha.desc fun j hj => by
    rw [hτ j hj]
    split_ifs
    exacts [h₁₂, h₀₂]
  have hface : ∀ (j : Fin 3) (hj : j ≠ 2), (DiagSet.toSSet.obj X).δ j
      (SSet.yonedaEquiv σ) = if j = 0 then e₁₂.edge else e₀₂.edge := fun j hj =>
    (SSet.stdSimplex.yonedaEquiv_δ_comp σ j).symm.trans
      ((congrArg (fun f => SSet.yonedaEquiv (f ≫ σ)) (SSet.horn.ι_ι 2 j hj).symm).trans
        ((congrArg (fun f => SSet.yonedaEquiv (SSet.horn.ι 2 j hj ≫ f)) hσ).trans (hτ j hj)))
  obtain ⟨y₀, y₁, y₂, f₀₁, f₁₂, f₀₂, h, hs⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv σ)
  have h₀ : f₁₂.edge = e₁₂.edge := h.d₀.symm.trans (hs ▸ hface 0 (by decide))
  have h₁ : f₀₂.edge = e₀₂.edge := h.d₁.symm.trans (hs ▸ hface 1 (by decide))
  obtain rfl : y₁ = x₁ := f₁₂.src_eq.symm.trans ((congrArg _ h₀).trans e₁₂.src_eq)
  obtain rfl : y₂ = x₂ := f₁₂.tgt_eq.symm.trans ((congrArg _ h₀).trans e₁₂.tgt_eq)
  obtain rfl : y₀ = x₀ := f₀₂.src_eq.symm.trans ((congrArg _ h₁).trans e₀₂.src_eq)
  obtain rfl : f₁₂ = e₁₂ := SSet.Edge.ext h₀
  obtain rfl : f₀₂ = e₀₂ := SSet.Edge.ext h₁
  exact ⟨f₀₁, ⟨h⟩⟩

theorem isEquivalence_id_edge (X : DiagSet.{u}) (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    IsEquivalence X ((SSet.Edge.id x).edge : diagram X (atomSimplex 1)) := by
  refine degenerate_isEquivalence X _ ⟨atomSimplex 0, simplexHom (SimplexCategory.σ 0).toOrderHom,
    x, isCollapseHom_simplexHom_of_surjective _ (SimplexCategory.epi_iff_surjective.1
      inferInstance), fun h => ?_, rfl⟩
  have h₁ := Atom.dimension_eq_of_iso
    (@asIso _ _ _ _ (simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom) h)
  have h₂ := card_atomSimplexVertices (atomSimplex 1).top
  have h₃ := card_atomSimplexVertices (atomSimplex 0).top
  rw [atomSimplexVertices_top, Finset.card_univ, Fintype.card_fin] at h₂ h₃
  rw [(atomSimplex 1).dimension_eq, (atomSimplex 0).dimension_eq] at h₁
  omega

theorem nonempty_invStruct_of_isEquivalence {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (f : SSet.Edge x y)
    (hf : IsEquivalence X (f.edge : diagram X (atomSimplex 1))) : Nonempty f.InvStruct := by
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj X ((isFibrant_infty_iff 1 X).2 hX)
  obtain ⟨g, ⟨h₁⟩⟩ := exists_compStruct_of_isEquivalence_horn_zero hX f (SSet.Edge.id x) hf
    (isEquivalence_id_edge X x)
  obtain ⟨g', ⟨h₂⟩⟩ := exists_compStruct_of_isEquivalence_horn_two hX f (SSet.Edge.id y) hf
    (isEquivalence_id_edge X y)
  have e₁ := (SSet.Truncated.HomotopyCategory.homMk_comp_homMk h₁).trans
    (SSet.Truncated.HomotopyCategory.homMk_id _)
  have e₂ := (SSet.Truncated.HomotopyCategory.homMk_comp_homMk h₂).trans
    (SSet.Truncated.HomotopyCategory.homMk_id _)
  have hgg' : SSet.Truncated.HomotopyCategory.homMk g = SSet.Truncated.HomotopyCategory.homMk g' :=
    (Category.id_comp _).symm.trans ((congrArg (· ≫ _) e₂.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) e₁).trans (Category.comp_id _))))
  exact (SSet.isIso_homMk_iff f).1 ⟨SSet.Truncated.HomotopyCategory.homMk g, e₁,
    (congrArg (· ≫ _) hgg').trans e₂⟩

end Edges

section Endpoint

open Atoms.Molecule Atoms.Molecule.OGP Simplicial Opposite

theorem weakEquivalence_flat_map_hornInclusion_comp_markingInclusion (n : ℕ∞) (H : HornData)
    (hH : ∃ m : MarkedHornData, m.toHornData = H)
    (h0 : ∀ a ∈ hornSubset H, grade ℕ a = 0) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive.{u} n).map
      ((MarkedPresheaf.flat atomMarking).map (hornInclusion H) ≫
        MarkedDiagSet.markingInclusion H.atom H.positive)) := by
  obtain ⟨m, rfl⟩ := hH
  have hmark : m.marking = ∅ := Set.eq_empty_of_forall_notMem fun a ha =>
    absurd (h0 a (m.marking_mem a ha).1) (Nat.pos_iff_ne_zero.1 (m.marking_mem a ha).2)
  have hdeg : ∀ {V : Atom} {Z Z' : DiagSet.{u}} (e : Z ≅ Z') (x : Z.obj (op V)),
      IsDegenerate Z' (e.hom.app (op V) x) ↔ IsDegenerate Z x := fun e x => by
    refine ⟨fun h => ?_, isDegenerate_app e.hom⟩
    have hx : e.inv.app _ (e.hom.app _ x) = x := Iso.hom_inv_id_app_apply e _ x
    exact hx ▸ isDegenerate_app e.inv h
  let src : m.source ≅ (MarkedPresheaf.flat atomMarking).obj (horn m.toHornData) :=
    markedIsoMk (Iso.refl _) fun V x => by
      refine ((MarkedPresheaf.mem_marked_ofMarking _ _ V _).trans ?_).trans
        (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V _).symm
      exact ⟨fun h => h.elim id fun ⟨a, ha, _⟩ => absurd (hmark ▸ ha) (Set.notMem_empty a),
        Or.inl⟩
  let tgt : m.target ≅ MarkedDiagSet.markedAtom m.atom m.positive :=
    markedIsoMk (closedSubpresheafUnivIso m.atom) fun V x => by
      refine ((MarkedPresheaf.mem_marked_ofMarking _ _ V _).trans ?_).trans
        (MarkedPresheaf.mem_marked_ofMarking _ _ V _).symm
      refine or_congr (hdeg (closedSubpresheafUnivIso m.atom) x).symm ⟨?_, fun h => ?_⟩
      · rintro ⟨a, ha, him, hd⟩
        rcases m.mem_targetMarking_iff.1 ha with rfl | ⟨hsub, -⟩ | ha
        · have ht := apply_top_eq_of_map_eq x.1.down him
          exact isIso_of_isCollapseHom_of_dimension_eq _ (isCollapseHom_of_apply_eq_top _ ht)
            (hd.trans m.atom.dimension_eq.symm)
        · obtain ⟨y, hy⟩ := m.atom.isMolecule.nonempty_faces LowerSet.mem_top
            (by rw [← m.atom.dimension_eq]; exact m.positive) (!m.side)
          rw [hmark] at hsub
          exact absurd (hsub hy) (Set.notMem_empty y)
        · rw [hmark] at ha
          exact absurd ha (Set.notMem_empty a)
      · refine ⟨m.atom.top, m.mem_targetMarking_iff.2 (Or.inl rfl), ?_, ?_⟩
        · exact (Atom.map_top _).trans (congrArg LowerSet.Iic
            (iso_hom_apply_top (@asIso _ _ _ _ (x.1.down : V ⟶ m.atom) h)))
        · rw [← m.atom.dimension_eq]
          exact Atom.dimension_eq_of_iso (@asIso _ _ _ _ (x.1.down : V ⟶ m.atom) h)
  have E : Arrow.mk (markedHornInclusion m) ≅ Arrow.mk
      ((MarkedPresheaf.flat atomMarking).map (hornInclusion m.toHornData) ≫
        MarkedDiagSet.markingInclusion m.atom m.positive) :=
    Arrow.isoMk src tgt (MarkedPresheaf.hom_ext rfl)
  have hm : markedExactCylinder.{u}.weakEquivalences (coinductiveGenerators n)
      (markedHornInclusion m) :=
    markedExactCylinder.{u}.anodyne_le_weakEquivalences _ (coinductiveGenerators_le_monomorphisms n)
      _ (markedExactCylinder.{u}.le_anodyne _ _ (by
        unfold coinductiveGenerators
        exact (le_sup_left.trans le_sup_left : markedHorns ≤ _) _ (MorphismProperty.ofHoms.mk m)))
  have := MorphismProperty.respectsIso_of_isStableUnderComposition
    (markedExactCylinder.{u}.isomorphisms_le_weakEquivalences (coinductiveGenerators n))
  exact (weakEquivalence_iff _).2
    (((markedExactCylinder.{u}.weakEquivalences _).arrow_mk_iso_iff E).1 hm)

def vertexToHorn :
    ball (atomSimplex 0) ⟶ horn (simplexHornData 0 0).toHornData :=
  Subfunctor.lift (uliftYoneda.{u}.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom)) (by
    rintro U _ ⟨⟨c : U.unop ⟶ atomSimplex 0⟩, rfl⟩ t
    refine (mem_hornSubset_simplexHornData_iff 0 0 _).2 ⟨1, by decide, fun h => ?_⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 ((congrArg (1 ∈ ·)
      (atomSimplexVertices_simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom (c t))).mp h)
    exact absurd hi (Fin.succAbove_ne 1 i))

instance isIso_vertexToHorn : IsIso vertexToHorn.{u} := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [CategoryTheory.isIso_iff_bijective]
  have hmono : Mono (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom) :=
    mono_of_isInclusionHom _ (isInclusionHom_simplexHom_of_injective _
      (SimplexCategory.mono_iff_injective.1 inferInstance))
  refine ⟨fun c c' h => ULift.ext _ _
    ((cancel_mono (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom)).1
      (congrArg ULift.down (congrArg Subtype.val h))), fun y => ?_⟩
  obtain ⟨j, hj, hy⟩ := (mem_hornSubset_simplexHornData_iff 0 0 _).1 (y.2 U.unop.top)
  have hj₁ := j.isLt
  have hj₀ : j.val ≠ 0 := fun h => hj (Fin.ext h)
  obtain rfl : j = 1 := Fin.ext (by change j.val = 1; omega)
  obtain ⟨g, hg⟩ := (exists_comp_simplexHom_eq_iff (e := (SimplexCategory.δ (1 : Fin 2)).toOrderHom)
    (SimplexCategory.mono_iff_injective.1 inferInstance) y.1.down).2 (by
      rw [show Finset.univ.image (SimplexCategory.δ (1 : Fin 2)).toOrderHom = {1}ᶜ from
        Fin.image_succAbove_univ 1]
      intro i hi
      rw [Finset.mem_compl, Finset.mem_singleton]
      rintro rfl
      exact hy hi)
  exact ⟨⟨g⟩, Subtype.ext (ULift.ext _ _ hg)⟩

theorem weakEquivalence_yoneda_map_comp_toWalkingEquivalence :
    WeakEquivalence ((DiagSet.toInfty 1).map
      (uliftYoneda.{u}.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom) ≫
        toWalkingEquivalence (atomSimplex 1) dimension_atomSimplex_one_pos)) := by
  let F := MarkedDiagSet.toCoinductive 1
  refine (weakEquivalence_flat_map_iff 1 _).1 ?_
  let H := (simplexHornData 0 0).toHornData
  have hH := weakEquivalence_flat_map_hornInclusion_comp_markingInclusion 1 H
    (AtomicHornData.exists_markedHornData _) fun a ha => by
      obtain ⟨j, hj, hy⟩ := (mem_hornSubset_simplexHornData_iff 0 0 a).1 ha
      have h₁ := card_atomSimplexVertices a
      have h₂ : atomSimplexVertices (0 + 1) a ⊆ {j}ᶜ := fun i hi => by
        rw [Finset.mem_compl, Finset.mem_singleton]
        rintro rfl
        exact hy hi
      have h₃ := Finset.card_le_card h₂
      rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin, h₁] at h₃
      exact Nat.le_zero.1 (Nat.le_of_succ_le_succ h₃)
  have hloc : weakEquivalences (MarkedDiagSet.Coinductive 1)
      (F.map (MarkedDiagSet.flatToMarkedWalkingEquivalence (atomSimplex 1)
        dimension_atomSimplex_one_pos)) :=
    (weakEquivalence_iff _).1 (weakEquivalence_of_hasLiftingProperty _
      fun _ _ _ _ _ hp => hasLiftingProperty_of_coinductiveGenerators 1
        (Or.inr (MorphismProperty.ofHoms.mk (⟨atomSimplex 1, dimension_atomSimplex_one_pos⟩ :
          {U : Atom // 0 < U.dimension}))) hp.mem)
  have hW := (weakEquivalence_iff _).1 (weakEquivalence_markedAtomToMarkedWalkingEquivalence 1
    (atomSimplex 1) dimension_atomSimplex_one_pos)
  have h₁ : weakEquivalences (MarkedDiagSet.Coinductive 1) (F.map
      ((MarkedPresheaf.flat atomMarking).map (hornInclusion H ≫
        toWalkingEquivalence (atomSimplex 1) dimension_atomSimplex_one_pos))) := by
    refine (weakEquivalences _).of_postcomp _ _ hloc ?_
    have e : F.map ((MarkedPresheaf.flat atomMarking).map (hornInclusion H ≫
        toWalkingEquivalence (atomSimplex 1) dimension_atomSimplex_one_pos)) ≫
          F.map (MarkedDiagSet.flatToMarkedWalkingEquivalence _ dimension_atomSimplex_one_pos) =
        F.map ((MarkedPresheaf.flat atomMarking).map (hornInclusion H) ≫
          MarkedDiagSet.markingInclusion H.atom H.positive) ≫
          F.map (MarkedDiagSet.markedAtomToMarkedWalkingEquivalence _
            dimension_atomSimplex_one_pos) :=
      MarkedPresheaf.hom_ext rfl
    rw [e]
    exact (weakEquivalences _).comp_mem _ _ ((weakEquivalence_iff _).1 hH) hW
  have h₀ : weakEquivalences (MarkedDiagSet.Coinductive 1)
      (F.map ((MarkedPresheaf.flat atomMarking).map vertexToHorn)) :=
    markedExactCylinder.{u}.isomorphisms_le_weakEquivalences _
      ((MarkedPresheaf.flat atomMarking).map vertexToHorn)
      (MorphismProperty.isomorphisms.infer_property _)
  have e : uliftYoneda.{u}.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom) ≫
      toWalkingEquivalence (atomSimplex 1) dimension_atomSimplex_one_pos =
        vertexToHorn ≫ hornInclusion H ≫ toWalkingEquivalence (atomSimplex 1)
          dimension_atomSimplex_one_pos := rfl
  refine (weakEquivalence_iff _).2 ((congrArg (fun f => weakEquivalences
    (MarkedDiagSet.Coinductive 1) (F.map ((MarkedPresheaf.flat atomMarking).map f))) e).mpr ?_)
  exact (congrArg (fun g => weakEquivalences (MarkedDiagSet.Coinductive 1) (F.map g))
    ((MarkedPresheaf.flat atomMarking).map_comp vertexToHorn (hornInclusion H ≫
      toWalkingEquivalence (atomSimplex 1) dimension_atomSimplex_one_pos))).mpr
    ((weakEquivalences _).comp_mem _ _ h₀ h₁)

theorem exists_isEquivalence_lift {X Y : DiagSet.{u}} (p : X ⟶ Y)
    (hp : Fibration ((DiagSet.toInfty 1).map p)) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (x₀ : X.obj (op (atomSimplex 0)))
    (b : Y.obj (op (atomSimplex 1))) (hb : IsEquivalence Y b)
    (hsrc : Y.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom).op b = p.app _ x₀) :
    ∃ a : X.obj (op (atomSimplex 1)), IsEquivalence X a ∧
      X.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom).op a = x₀ ∧
        p.app _ a = b := by
  obtain ⟨φ, hφ⟩ := (exists_toWalkingEquivalence_comp_eq_iff _ dimension_atomSimplex_one_pos
    hY.1 b).2 hb
  let F := DiagSet.toInfty 1
  have := weakEquivalence_yoneda_map_comp_toWalkingEquivalence
  have hmono : Mono (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom) :=
    mono_of_isInclusionHom _ (isInclusionHom_simplexHom_of_injective _
      (SimplexCategory.mono_iff_injective.1 inferInstance))
  have hW : Mono (toWalkingEquivalence (atomSimplex 1) dimension_atomSimplex_one_pos) :=
    InversionData.mono_toLocalization (topInversionData (atomSimplex 1)
      dimension_atomSimplex_one_pos)
  have : Cofibration (F.map
      (uliftYoneda.{u}.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom) ≫
      toWalkingEquivalence (atomSimplex 1) dimension_atomSimplex_one_pos)) :=
    (cofibration_iff _).2 (@mono_comp _ _ _ _ _ _ (uliftYoneda.{u}.map_mono _) _ hW)
  have sq : CommSq (F.map (uliftYonedaEquiv.symm x₀)) (F.map (uliftYoneda.{u}.map (simplexHom
      (SimplexCategory.δ (1 : Fin 2)).toOrderHom) ≫ toWalkingEquivalence (atomSimplex 1)
        dimension_atomSimplex_one_pos)) (F.map p) (F.map φ) := ⟨uliftYonedaEquiv.injective
    (((congrArg (p.app _) (uliftYonedaEquiv.apply_symm_apply x₀)).trans hsrc.symm).trans
      ((congrArg (Y.map _) (uliftYonedaEquiv.apply_symm_apply b).symm).trans
        ((uliftYonedaEquiv_naturality _ _).trans (congrArg uliftYonedaEquiv
          ((congrArg (_ ≫ ·) hφ.symm).trans (Category.assoc _ _ _).symm)))))⟩
  refine ⟨uliftYonedaEquiv (toWalkingEquivalence _ _ ≫ sq.lift), ?_, ?_, ?_⟩
  · exact (exists_toWalkingEquivalence_comp_eq_iff _ _ hX.1 _).1
      ⟨sq.lift, (uliftYonedaEquiv.symm_apply_apply _).symm⟩
  · exact (uliftYonedaEquiv_naturality _ _).trans ((congrArg uliftYonedaEquiv
      ((Category.assoc _ _ _).symm.trans sq.fac_left)).trans (Equiv.apply_symm_apply _ _))
  · exact (uliftYonedaEquiv_comp _ p).symm.trans ((congrArg uliftYonedaEquiv
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq.fac_right).trans hφ))).trans
        (Equiv.apply_symm_apply _ _))

end Endpoint

section Triangles

open Atoms.Molecule Atoms.Molecule.OGP Simplicial Opposite PastingDiagram Order

theorem equiv_boundary_ofCell_map {Y : DiagSet.{u}} {U V : Atom} (z : Y.obj (op U)) (f : V ⟶ U)
    (hf : IsInclusionHom f) {k : ℕ} (hk : V.dimension ≤ k) {α : Bool}
    (h : Atom.map f ⊤ = U.ogp.boundary ⊤ k α) :
    ((ofCell z).boundary k α).Equiv (ofCell (Y.map f.op z)) := by
  let φ : V.ogp ⟶ U.ogp := ConcreteCategory.ofHom ⟨f, Atom.isMorphism_of_isInclusionHom f hf⟩
  have : IsInclusion φ := ⟨hf⟩
  have hφ : RDCpx.ofInclusion (P := V.toMoleculeShape.rdc) (Q := U.toMoleculeShape.rdc) φ =
      atomToRDCpx.map f := by
    ext x
    rfl
  refine (equiv_boundary_of_emb (ofCell (Y.map f.op z)) (ofCell z) φ
    ((congrArg (realize.map · ≫ (ofCell z).map) hφ).trans (ofCell_map_op_map f z).symm)
    (k := k) (α := α) ?_).trans (equiv_boundary_dim _ hk α)
  rw [boundary_eq_self (by
    rw [LowerSet.krullDim_top]
    exact V.toMoleculeShape.krullDim_eq_dimension.trans_le (by exact_mod_cast hk)) α]
  exact h

theorem equiv_boundary_false_ofCell_atomSimplex_two {Y : DiagSet.{u}}
    (z : Y.obj (op (atomSimplex 2))) :
    ((ofCell z).boundary 1 false).Equiv
      (ofCell (Y.map (simplexHom (SimplexCategory.δ (1 : Fin 3)).toOrderHom).op z)) := by
  refine equiv_boundary_ofCell_map z _ (isInclusionHom_simplexHom_of_injective _
    (SimplexCategory.mono_iff_injective.1 inferInstance)) (dimension_atomSimplex 1).le ?_
  rw [Atom.map_top, boundary_univ_one_atomSimplex_two, ← lowerClosure_singleton]
  congr 1
  ext x
  rw [Set.mem_singleton_iff, mem_faceSet_top_atomSimplex_iff 1 false x]
  constructor
  · rintro rfl
    exact ⟨1, rfl, rfl⟩
  · rintro ⟨k, rfl, hk⟩
    fin_cases k
    · exact absurd hk (by decide)
    · rfl
    · exact absurd hk (by decide)

theorem equiv_boundary_ofCell_atomSimplex_one {Y : DiagSet.{u}} (c : Y.obj (op (atomSimplex 1)))
    (α : Bool) : ((ofCell c).boundary 0 α).Equiv
      (ofCell (Y.map (simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom).op c)) :=
  equiv_boundary_ofCell_map c _ (isInclusionHom_simplexHom_of_injective _
    (SimplexCategory.mono_iff_injective.1 inferInstance)) (dimension_atomSimplex 0).le
    (SetLike.coe_injective (Set.image_univ.trans (image_univ_simplexHom_δ_atomSimplex_one α)))

theorem map_δ_map_δ_atomSimplex_two {Y : DiagSet.{u}} (z : Y.obj (op (atomSimplex 2))) :
    Y.map (simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom).op
        (Y.map (simplexHom (SimplexCategory.δ (2 : Fin 3)).toOrderHom).op z) =
      Y.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom).op
        (Y.map (simplexHom (SimplexCategory.δ (0 : Fin 3)).toOrderHom).op z) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    ← simplexHom_comp, ← simplexHom_comp]
  congr 3

theorem pastable_ofCell_atomSimplex_two {Y : DiagSet.{u}} (z : Y.obj (op (atomSimplex 2))) :
    (ofCell (Y.map (simplexHom (SimplexCategory.δ (2 : Fin 3)).toOrderHom).op z)).Pastable
      (ofCell (Y.map (simplexHom (SimplexCategory.δ (0 : Fin 3)).toOrderHom).op z)) 0 := by
  refine ⟨(equiv_boundary_ofCell_atomSimplex_one _ true).trans ?_, ?_⟩
  · refine Eq.mpr (congrArg (fun c => (ofCell c).Equiv _) (map_δ_map_δ_atomSimplex_two z)) ?_
    exact (equiv_boundary_ofCell_atomSimplex_one _ false).symm
  · change 0 < min (atomSimplex 1).dimension (atomSimplex 1).dimension
    rw [dimension_atomSimplex]
    omega

theorem equiv_boundary_true_ofCell_atomSimplex_two {Y : DiagSet.{u}}
    (z : Y.obj (op (atomSimplex 2))) :
    ((ofCell z).boundary 1 true).Equiv
      ((ofCell (Y.map (simplexHom (SimplexCategory.δ (2 : Fin 3)).toOrderHom).op z)).paste
        (ofCell (Y.map (simplexHom (SimplexCategory.δ (0 : Fin 3)).toOrderHom).op z)) 0
        (pastable_ofCell_atomSimplex_two z)) := by
  have h₂ : Function.Injective (SimplexCategory.δ (2 : Fin 3)).toOrderHom :=
    SimplexCategory.mono_iff_injective.1 inferInstance
  have h₀ : Function.Injective (SimplexCategory.δ (0 : Fin 3)).toOrderHom :=
    SimplexCategory.mono_iff_injective.1 inferInstance
  refine (equiv_paste_of_emb _ _ ((ofCell z).boundary 1 true) 0
    (pastable_ofCell_atomSimplex_two z) (ofCell z).map
    ((ofCell z).shape.boundaryIncl 1 true) (simplexHomEmb _ h₂) (simplexHomEmb _ h₀)
    (boundary_map _ 1 true) (ofCell_map_op_map _ z).symm (ofCell_map_op_map _ z).symm ?_).symm
  have hI (f : Fin 2 →o Fin 3) (hf : Function.Injective f) :
      map (simplexHomEmb f hf) ⊤ = LowerSet.Iic (simplexHom f (atomSimplex 1).top) := by
    rw [← (atomSimplex 1).Iic_top, map_Iic]
    rfl
  rw [hI _ h₂, hI _ h₀, MoleculeShape.map_boundaryIncl_top]
  exact isPastingIn_atomSimplex_two

theorem equiv_unit_ofCell_atomSimplex_zero {Y : DiagSet.{u}} (v : Y.obj (op (atomSimplex 0))) :
    (ofCell v).unit.Equiv
      (ofCell (Y.map (simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom).op v)) := by
  have hV : IsAtom (ofCell v).unit.shape.ogp :=
    isAtom_unitShape_of_dimension_eq_zero _ (dimension_atomSimplex 0)
  have hdV : (ofCell v).unit.shape.dimension = 0 + 1 := by
    change (ofCell v).unit.dim = 0 + 1
    rw [dim_unit]
    exact congrArg (· + 1) (dimension_atomSimplex 0)
  have hdW : (atomSimplex 1).toMoleculeShape.dimension = 0 + 1 := dimension_atomSimplex 1
  have hb : ∀ (V : MoleculeShape) (α : Bool),
      krullDim (⊤ : LowerSet (V.boundary 0 α).ogp) = 0 := fun V α => by
    rw [LowerSet.krullDim_top, MoleculeShape.krullDim_eq_dimension,
      MoleculeShape.dimension_boundary _ (Nat.zero_le _) α, Nat.cast_zero]
  obtain ⟨φ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso (ofCell v).unit.shape
    (atomSimplex 1).toMoleculeShape (n := 0)
    (fun α => (nonempty_iso_of_krullDim_eq_zero ((ofCell v).unit.shape.boundary 0 α).isMolecule
      ((atomSimplex 1).toMoleculeShape.boundary 0 α).isMolecule (hb _ α) (hb _ α)).some)
    hV (atomSimplex 1).isAtom hdV hdW
  refine ⟨φ, (congrArg (realize.map (RDCpx.isoOfIso (P := (ofCell v).unit.shape.rdc)
    (Q := (atomSimplex 1).toMoleculeShape.rdc) φ).hom ≫ ·) (ofCell_map_op_map _ v)).trans ?_⟩
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (ofCell v).map)
    (realize.map_comp _ _).symm).trans (congrArg (fun t => realize.map t ≫ (ofCell v).map) ?_))
  ext x
  exact (eq_top_atomSimplex_zero _).trans (eq_top_atomSimplex_zero _).symm

theorem pastable_ofCell_atomSimplex_one {Y : DiagSet.{u}} (a b : Y.obj (op (atomSimplex 1)))
    (h : Y.map (simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom).op a =
      Y.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom).op b) :
    (ofCell a).Pastable (ofCell b) 0 := by
  refine ⟨(equiv_boundary_ofCell_atomSimplex_one a true).trans ?_, ?_⟩
  · refine Eq.mpr (congrArg (fun c => (ofCell c).Equiv _) h) ?_
    exact (equiv_boundary_ofCell_atomSimplex_one b false).symm
  · change 0 < min (atomSimplex 1).dimension (atomSimplex 1).dimension
    rw [dimension_atomSimplex]
    omega

theorem isEquivalence_of_simplices {Y : DiagSet.{u}} (hY : IsInftyCategory 1 Y)
    (x y : Y.obj (op (atomSimplex 0))) (e g : Y.obj (op (atomSimplex 1)))
    (s₁ s₂ : Y.obj (op (atomSimplex 2)))
    (hex : Y.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom).op e = x)
    (hey : Y.map (simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom).op e = y)
    (hgy : Y.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom).op g = y)
    (hgx : Y.map (simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom).op g = x)
    (f₁₀ : Y.map (simplexHom (SimplexCategory.δ (0 : Fin 3)).toOrderHom).op s₁ = g)
    (f₁₁ : Y.map (simplexHom (SimplexCategory.δ (1 : Fin 3)).toOrderHom).op s₁ =
      Y.map (simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom).op x)
    (f₁₂ : Y.map (simplexHom (SimplexCategory.δ (2 : Fin 3)).toOrderHom).op s₁ = e)
    (f₂₀ : Y.map (simplexHom (SimplexCategory.δ (0 : Fin 3)).toOrderHom).op s₂ = e)
    (f₂₁ : Y.map (simplexHom (SimplexCategory.δ (1 : Fin 3)).toOrderHom).op s₂ =
      Y.map (simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom).op y)
    (f₂₂ : Y.map (simplexHom (SimplexCategory.δ (2 : Fin 3)).toOrderHom).op s₂ = g) :
    IsEquivalence Y e := by
  have h2 : ∀ s : Y.obj (op (atomSimplex 2)), cellRound s ∈ equivalences Y := fun s =>
    hY.2 (atomSimplex 2) s (by rw [dimension_atomSimplex]; exact_mod_cast (by omega : 1 < 2))
  have hd : (cellRound e).dim = 1 := dimension_atomSimplex 1
  have hd1 : (cellRound e).dim - 1 = 0 := by rw [hd]
  have hd₂ : (cellRound s₁).dim = 1 + 1 := dimension_atomSimplex 2
  have cellEquiv : ∀ {U : Atom} {a b : Y.obj (op U)}, a = b → (ofCell a).Equiv (ofCell b) :=
    fun h => h ▸ PastingDiagram.Equiv.refl _
  have bdry : ∀ {u w : PastingDiagram Y} {k k' : ℕ} {β : Bool}, k = k' →
      (u.boundary k β).Equiv w → (u.boundary k' β).Equiv w := by
    rintro _ _ _ _ _ rfl h
    exact h
  have bdry₂ : ∀ {u w : PastingDiagram Y} {k k' j j' : ℕ} {β γ : Bool}, k = k' → j = j' →
      (u.boundary k β).Equiv (w.boundary j γ) → (u.boundary k' β).Equiv (w.boundary j' γ) := by
    rintro _ _ _ _ _ _ _ _ rfl rfl h
    exact h
  have bdryUnit : ∀ {u w : PastingDiagram Y} {k k' j j' : ℕ} {β γ : Bool}, k = k' → j = j' →
      (u.boundary k β).Equiv (w.boundary j γ).unit →
        (u.boundary k' β).Equiv (w.boundary j' γ).unit := by
    rintro _ _ _ _ _ _ _ _ rfl rfl h
    exact h
  have pasteIdx : ∀ {u v w : PastingDiagram Y} {k k' : ℕ} (h : u.Pastable v k)
      (h' : u.Pastable v k'), k = k' → w.Equiv (u.paste v k h) → w.Equiv (u.paste v k' h') := by
    rintro _ _ _ _ _ _ _ rfl h
    exact h
  have pastIdx : ∀ {u v : PastingDiagram Y} {k k' : ℕ}, k = k' → u.Pastable v k →
      u.Pastable v k' := by
    rintro _ _ _ _ rfl h
    exact h
  have peg : (ofCell e).Pastable (ofCell g) 0 :=
    pastable_ofCell_atomSimplex_one e g (hey.trans hgy.symm)
  have pge : (ofCell g).Pastable (ofCell e) 0 :=
    pastable_ofCell_atomSimplex_one g e (hgx.trans hex.symm)
  have hs₁f : ((ofCell s₁).boundary 1 false).Equiv
      (ofCell (Y.map (simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom).op x)) :=
    (equiv_boundary_false_ofCell_atomSimplex_two s₁).trans (cellEquiv f₁₁)
  have hs₁t : ((ofCell s₁).boundary 1 true).Equiv ((ofCell e).paste (ofCell g) 0 peg) :=
    (equiv_boundary_true_ofCell_atomSimplex_two s₁).trans
      (PastingDiagram.Equiv.paste (cellEquiv f₁₂) (cellEquiv f₁₀) _ peg)
  have hs₂f : ((ofCell s₂).boundary 1 false).Equiv
      (ofCell (Y.map (simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom).op y)) :=
    (equiv_boundary_false_ofCell_atomSimplex_two s₂).trans (cellEquiv f₂₁)
  have hs₂t : ((ofCell s₂).boundary 1 true).Equiv ((ofCell g).paste (ofCell e) 0 pge) :=
    (equiv_boundary_true_ofCell_atomSimplex_two s₂).trans
      (PastingDiagram.Equiv.paste (cellEquiv f₂₂) (cellEquiv f₂₀) _ pge)
  have hux : (ofCell (Y.map (simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom).op x)).Equiv
      ((ofCell e).boundary 0 false).unit :=
    (equiv_unit_ofCell_atomSimplex_zero x).symm.trans (PastingDiagram.Equiv.unit
      ((cellEquiv hex).symm.trans (equiv_boundary_ofCell_atomSimplex_one e false).symm))
  have huy : (ofCell (Y.map (simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom).op y)).Equiv
      ((ofCell e).boundary 0 true).unit :=
    (equiv_unit_ofCell_atomSimplex_zero y).symm.trans (PastingDiagram.Equiv.unit
      ((cellEquiv hey).symm.trans (equiv_boundary_ofCell_atomSimplex_one e true).symm))
  obtain ⟨z, hz⟩ := exists_isWeakInverse (h2 s₁)
  obtain ⟨-, hzb⟩ := hz.hasBdry
    (x := ofCell (Y.map (simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom).op x))
    (y := (ofCell e).paste (ofCell g) 0 peg) ⟨hd₂, dimension_atomSimplex 1,
      (dim_paste _ _ _ _).trans (by
        rw [show (ofCell e).dim = 1 from dimension_atomSimplex 1,
          show (ofCell g).dim = 1 from dimension_atomSimplex 1]
        rfl),
      hs₁f, hs₁t⟩
  obtain ⟨hzr, hzm⟩ := hz.mem_equivalences fun _ => h2 s₁
  refine (mem_equivalences_iff _).2 (BiInvData.witness
    { dim_pos := hd.symm ▸ Nat.one_pos
      inverse := fun _ => cellRound g
      invertor := fun α => cond α (cellRound s₂) ⟨z.toPastingDiagram, hzr⟩
      invertor_mem := fun α => by cases α; exacts [hzm, h2 s₂]
      dim_inverse := fun _ => (dimension_atomSimplex 1).trans hd.symm
      dim_invertor := fun α => by
        cases α
        · exact hzb.dim_h.trans (congrArg (· + 1) hd.symm)
        · exact (dimension_atomSimplex 2).trans (congrArg (· + 1) hd.symm)
      equiv_boundary_inverse := fun _ γ => bdry₂ hd1.symm hd1.symm
        ((equiv_boundary_ofCell_atomSimplex_one g γ).trans ((cellEquiv (by
          cases γ
          exacts [hgy.trans hey.symm, hgx.trans hex.symm])).trans
            (equiv_boundary_ofCell_atomSimplex_one e (!γ)).symm))
      pastable := fun α => by
        cases α
        exacts [pastIdx hd1.symm peg, pastIdx hd1.symm pge]
      boundary_invertor_composite := fun α => by
        cases α
        · exact bdry hd.symm (pasteIdx peg _ hd1.symm hzb.side)
        · exact bdry hd.symm (pasteIdx pge _ hd1.symm hs₂t)
      boundary_invertor_unit := fun α => by
        cases α
        · exact bdryUnit hd.symm hd1.symm (hzb.other.trans hux)
        · exact bdryUnit hd.symm hd1.symm (hs₂f.trans huy) })

theorem isEquivalence_of_invStruct {Y : DiagSet.{u}} (hY : IsInftyCategory 1 Y)
    {x y : (DiagSet.toSSet.obj Y) _⦋0⦌} (f : SSet.Edge x y) (hf : Nonempty f.InvStruct) :
    IsEquivalence Y (f.edge : diagram Y (atomSimplex 1)) := by
  obtain ⟨I⟩ := hf
  exact isEquivalence_of_simplices hY x y f.edge I.inv.edge I.homInvId.simplex
    I.invHomId.simplex f.src_eq f.tgt_eq I.inv.src_eq I.inv.tgt_eq I.homInvId.d₀ I.homInvId.d₁
    I.homInvId.d₂ I.invHomId.d₀ I.invHomId.d₁ I.invHomId.d₂

end Triangles

theorem exists_isEquivalence_edge_lift {X Y : DiagSet.{u}} (p : X ⟶ Y)
    (hp : Fibration ((DiagSet.toInfty 1).map p)) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (x : X.Vertex) {y : Y.Vertex}
    (e : Y.Edge (x.map p) y) (he : IsEquivalence Y e.cell) :
    ∃ (z : X.Vertex) (a : X.Edge x z), IsEquivalence X a.cell ∧ (a.map p).cell = e.cell := by
  let b := Y.edgeEquivSSet e
  obtain ⟨a, ha, hsrc, hpa⟩ := exists_isEquivalence_lift p hp hX hY x b.edge
    ((isEquivalence_map_iso_iff atomSimplexOneIsoGlobe e.cell).2 he) b.src_eq
  let a' : SSet.Edge (X := DiagSet.toSSet.obj X) x
      ((DiagSet.toSSet.obj X).δ 0 a) := SSet.Edge.mk a hsrc rfl
  refine ⟨_, X.edgeEquivSSet.symm a', ?_, ?_⟩
  · exact (isEquivalence_map_iso_iff atomSimplexOneIsoGlobe.symm a).2 ha
  · change p.app _ (X.map atomSimplexOneIsoGlobe.inv.op a) = e.cell
    have h := (NatTrans.naturality_apply p atomSimplexOneIsoGlobe.inv.op a).trans
      (congrArg (Y.map atomSimplexOneIsoGlobe.inv.op) hpa)
    simpa only [b, DiagSet.edgeEquivSSet_edge, ← Functor.map_comp_apply, ← op_comp,
      Iso.inv_hom_id, op_id, Functor.map_id_apply] using h

section Quillen

open Simplicial SSet.modelCategoryJoyal

theorem isofibration_toSSet_map {X Y : DiagSet.Infty.{u} 1} (p : X ⟶ Y)
    (hp : Fibration p) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) : SSet.Isofibration (DiagSet.Infty.toSSet.map p) where
  toInnerFibration := innerFibration_toSSet_map p hp
  exists_lift x₀ {_} g hg := by
    obtain ⟨a, ha, hsrc, hpa⟩ := exists_isEquivalence_lift p hp hX hY x₀ g.edge
      (isEquivalence_of_invStruct hY g hg) g.src_eq
    exact ⟨_, SSet.Edge.mk a hsrc rfl, nonempty_invStruct_of_isEquivalence hX _ ha, hpa⟩

theorem isQuillen_sSetDiagSetAdj :
    DiagSet.Infty.sSetDiagSetAdj.{u}.IsQuillen := by
  refine DiagSet.Infty.sSetDiagSetAdj.isQuillen_of_fibrations_between_fibrant
    (fun _ _ f (_ : Mono f) => SSet.toDiagSet.map_mono f) fun X Y p hX hY hp => ?_
  have := quasicategory_toSSet_obj X hX
  have := quasicategory_toSSet_obj Y hY
  exact (fibration_iff_isofibration _).2 (isofibration_toSSet_map p hp
    ((isFibrant_infty_iff 1 X).1 hX) ((isFibrant_infty_iff 1 Y).1 hY))

theorem isFibrant_toSSet_obj {Y : DiagSet.{u}} (hY : IsInftyCategory 1 Y) :
    IsFibrant (DiagSet.toSSet.obj Y) :=
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj Y)

end Quillen

end Atoms.Diagrammatic
