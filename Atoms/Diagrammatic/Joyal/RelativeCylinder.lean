import Atoms.Diagrammatic.Joyal.DimensionShift
import Atoms.Diagrammatic.Joyal.GrayTensorCartesian
import Atoms.Diagrammatic.Localization.Comparison
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Over

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
open Atoms.Homotopical Atoms.Shape Simplicial

universe u

namespace Atoms.Diagrammatic

noncomputable def relativeMappingSpaceRestrict {V A' A X : DiagSet.{u}} (j : V ⟶ A') (k : A' ⟶ A)
    (f : V ⟶ X) : relativeMappingSpace (j ≫ k) f ⟶ relativeMappingSpace j f :=
  pullback.map _ _ _ _ ((grayHomRestrict k).app X) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, grayHomRestrict_comp, NatTrans.comp_app])
    (by rw [Category.comp_id, Category.id_comp])

theorem isPullback_relativeMappingSpaceRestrict {V A' A X : DiagSet.{u}} (j : V ⟶ A')
    (k : A' ⟶ A) (f : V ⟶ X) :
    IsPullback (pullback.fst ((grayHomRestrict (j ≫ k)).app X) (diagramPoint f))
      (relativeMappingSpaceRestrict j k f) ((grayHomRestrict k).app X)
      (pullback.fst ((grayHomRestrict j).app X) (diagramPoint f)) := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
  have e₁ : relativeMappingSpaceRestrict j k f ≫ pullback.snd _ _ = pullback.snd _ _ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have e₂ : (grayHomRestrict k).app X ≫ (grayHomRestrict j).app X =
      (grayHomRestrict (j ≫ k)).app X := by
    rw [grayHomRestrict_comp, NatTrans.comp_app]
  rw [e₁, e₂]
  exact IsPullback.of_hasPullback _ _

noncomputable def relativeMappingSpaceMapOfEq {V A X Y : DiagSet.{u}} (i : V ⟶ A)
    {f : V ⟶ X} {g : V ⟶ Y} (p : X ⟶ Y) (h : f ≫ p = g) :
    relativeMappingSpace i f ⟶ relativeMappingSpace i g :=
  pullback.map _ _ _ _ ((grayHomRight A).map p) (𝟙 _) ((grayHomRight V).map p)
    ((grayHomRestrict i).naturality p).symm (by rw [Category.id_comp, diagramPoint_comp, h])

noncomputable def relativeMappingSpaceMap {V A X Y : DiagSet.{u}} (i : V ⟶ A) (f : V ⟶ X)
    (p : X ⟶ Y) : relativeMappingSpace i f ⟶ relativeMappingSpace i (f ≫ p) :=
  relativeMappingSpaceMapOfEq i p rfl

@[reassoc]
theorem relativeMappingSpaceMapOfEq_fst {V A X Y : DiagSet.{u}} (i : V ⟶ A)
    {f : V ⟶ X} {g : V ⟶ Y} (p : X ⟶ Y) (h : f ≫ p = g) :
    relativeMappingSpaceMapOfEq i p h ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (grayHomRight A).map p :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem relativeMappingSpaceMapOfEq_snd {V A X Y : DiagSet.{u}} (i : V ⟶ A)
    {f : V ⟶ X} {g : V ⟶ Y} (p : X ⟶ Y) (h : f ≫ p = g) :
    relativeMappingSpaceMapOfEq i p h ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem relativeMappingSpaceRestrict_mapOfEq {V A' A X Y : DiagSet.{u}}
    (j : V ⟶ A') (k : A' ⟶ A) {f : V ⟶ X} {g : V ⟶ Y}
    (p : X ⟶ Y) (h : f ≫ p = g) :
    relativeMappingSpaceRestrict j k f ≫ relativeMappingSpaceMapOfEq j p h =
      relativeMappingSpaceMapOfEq (j ≫ k) p h ≫ relativeMappingSpaceRestrict j k g := by
  apply pullback.hom_ext
  · simp only [Category.assoc, relativeMappingSpaceMapOfEq_fst,
      relativeMappingSpaceMapOfEq_fst_assoc,
      relativeMappingSpaceRestrict, pullback.lift_fst_assoc, pullback.lift_fst]
    rw [(grayHomRestrict k).naturality p]
  · simp only [Category.assoc, relativeMappingSpaceMapOfEq_snd,
      relativeMappingSpaceRestrict, pullback.lift_snd, Category.comp_id]

private theorem isPullback_relativeMappingSpaceMapOfEq {V A X Y : DiagSet.{u}} (i : V ⟶ A)
    {f : V ⟶ X} {g : V ⟶ Y} (p : X ⟶ Y) (h : f ≫ p = g) :
    IsPullback (pullback.fst ((grayHomRestrict i).app X) (diagramPoint f))
      (relativeMappingSpaceMapOfEq i p h)
      (pullback.lift ((grayHomRestrict i).app X) ((grayHomRight A).map p)
        ((grayHomRestrict i).naturality p).symm :
        (grayHomRight A).obj X ⟶ pullback ((grayHomRight V).map p) ((grayHomRestrict i).app Y))
      (pullback.lift (pullback.snd ((grayHomRestrict i).app Y) (diagramPoint g) ≫ diagramPoint f)
        (pullback.fst _ _) (by
          rw [Category.assoc, diagramPoint_comp, h, pullback.condition]) :
        relativeMappingSpace i g ⟶ pullback ((grayHomRight V).map p)
          ((grayHomRestrict i).app Y)) := by
  have hb : IsPullback (pullback.lift (pullback.snd ((grayHomRestrict i).app Y) (diagramPoint g) ≫
        diagramPoint f) (pullback.fst _ _) (by
          rw [Category.assoc, diagramPoint_comp, h, pullback.condition]) :
        relativeMappingSpace i g ⟶ pullback ((grayHomRight V).map p) ((grayHomRestrict i).app Y))
      (pullback.snd _ _) (pullback.fst _ _) (diagramPoint f) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
    rw [pullback.lift_snd, diagramPoint_comp, h]
    exact IsPullback.of_hasPullback _ _
  refine IsPullback.of_bot ?_ ?_ hb
  · rw [relativeMappingSpaceMapOfEq_snd, pullback.lift_fst]
    exact IsPullback.of_hasPullback _ _
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst,
        relativeMappingSpaceMapOfEq_snd_assoc, pullback.condition]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd,
        relativeMappingSpaceMapOfEq_fst]

theorem relativeMappingSpaceHomEquiv_comp {V A X : DiagSet.{u}} (i : V ⟶ A) (f : V ⟶ X)
    {T T' : DiagSet.{u}} (g : T' ⟶ T) (t : T ⟶ relativeMappingSpace i f) :
    (relativeMappingSpaceHomEquiv i f T' (g ≫ t)).1 =
      (grayTensorRight A).map g ≫ (relativeMappingSpaceHomEquiv i f T t).1 :=
  (congrArg _ (Category.assoc _ _ _)).trans
    ((grayTensorRightAdjunction A).homEquiv_naturality_left_symm _ _)

noncomputable def relativeMappingSpaceIsoOfIso {V V' A A' X : DiagSet.{u}} {i : V ⟶ A}
    {i' : V' ⟶ A'} (eV : V ≅ V') (eA : A ≅ A') (w : i ≫ eA.hom = eV.hom ≫ i')
    {f : V ⟶ X} {f' : V' ⟶ X} (hf : f = eV.hom ≫ f') :
    relativeMappingSpace i f ≅ relativeMappingSpace i' f' :=
  Yoneda.ext _ _
    (fun {T} t => (relativeMappingSpaceHomEquiv i' f' T).symm
      ⟨(grayTensorLeft T).map eA.inv ≫ (relativeMappingSpaceHomEquiv i f T t).1, by
        have w' : i' ≫ eA.inv = eV.inv ≫ i := by
          rw [Iso.comp_inv_eq, Category.assoc, w, Iso.inv_hom_id_assoc]
        rw [← Category.assoc, ← Functor.map_comp, w', Functor.map_comp, Category.assoc,
          (relativeMappingSpaceHomEquiv i f T t).2, ← Category.assoc,
          grayTensorLeft_map_grayTensorSnd, Category.assoc, hf, Iso.inv_hom_id_assoc]⟩)
    (fun {T} t => (relativeMappingSpaceHomEquiv i f T).symm
      ⟨(grayTensorLeft T).map eA.hom ≫ (relativeMappingSpaceHomEquiv i' f' T t).1, by
        rw [← Category.assoc, ← Functor.map_comp, w, Functor.map_comp, Category.assoc,
          (relativeMappingSpaceHomEquiv i' f' T t).2, ← Category.assoc,
          grayTensorLeft_map_grayTensorSnd, Category.assoc, hf]⟩)
    (fun {T} t => (relativeMappingSpaceHomEquiv i f T).injective (Subtype.ext (by
      rw [Equiv.apply_symm_apply]
      dsimp only
      rw [Equiv.apply_symm_apply, ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id]
      exact Category.id_comp _)))
    (fun {T} t => (relativeMappingSpaceHomEquiv i' f' T).injective (Subtype.ext (by
      rw [Equiv.apply_symm_apply]
      dsimp only
      rw [Equiv.apply_symm_apply, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id]
      exact Category.id_comp _)))
    (fun {T T'} g t => (relativeMappingSpaceHomEquiv i' f' T').injective (Subtype.ext (by
      rw [Equiv.apply_symm_apply]
      dsimp only
      rw [relativeMappingSpaceHomEquiv_comp, relativeMappingSpaceHomEquiv_comp,
        Equiv.apply_symm_apply]
      dsimp only
      rw [ ← Category.assoc, ← Category.assoc,
        grayTensorLeft_map_comp_grayTensorRight_map])))

theorem relativeMappingSpaceHomEquiv_relativeMappingSpaceIsoOfIso {V V' A A' X : DiagSet.{u}}
    {i : V ⟶ A} {i' : V' ⟶ A'} (eV : V ≅ V') (eA : A ≅ A') (w : i ≫ eA.hom = eV.hom ≫ i')
    {f : V ⟶ X} {f' : V' ⟶ X} (hf : f = eV.hom ≫ f') {T : DiagSet.{u}}
    (t : T ⟶ relativeMappingSpace i f) :
    (relativeMappingSpaceHomEquiv i' f' T (t ≫ (relativeMappingSpaceIsoOfIso eV eA w hf).hom)).1 =
      (grayTensorLeft T).map eA.inv ≫ (relativeMappingSpaceHomEquiv i f T t).1 := by
  have h : (relativeMappingSpaceHomEquiv i' f' _ (relativeMappingSpaceIsoOfIso eV eA w hf).hom).1 =
      (grayTensorLeft _).map eA.inv ≫ (relativeMappingSpaceHomEquiv i f _ (𝟙 _)).1 :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  rw [relativeMappingSpaceHomEquiv_comp, h, ← Category.assoc,
    ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc,
    ← relativeMappingSpaceHomEquiv_comp, Category.comp_id]

theorem relativeMappingSpaceHomEquiv_relativeMappingSpaceRestrict {V A' A X : DiagSet.{u}}
    (j : V ⟶ A') (k : A' ⟶ A) (f : V ⟶ X) {T : DiagSet.{u}}
    (t : T ⟶ relativeMappingSpace (j ≫ k) f) :
    (relativeMappingSpaceHomEquiv j f T (t ≫ relativeMappingSpaceRestrict j k f)).1 =
      (grayTensorLeft T).map k ≫ (relativeMappingSpaceHomEquiv (j ≫ k) f T t).1 := by
  refine ((grayTensorRightAdjunction A').homEquiv T X).injective ?_
  rw [← homEquiv_comp_grayHomRestrict]
  simp only [relativeMappingSpaceHomEquiv, Equiv.coe_fn_mk, Equiv.apply_symm_apply,
    Category.assoc, relativeMappingSpaceRestrict, pullback.lift_fst]

theorem relativeMappingSpaceHomEquiv_relativeMappingSpaceMapOfEq {V A X Y : DiagSet.{u}}
    (i : V ⟶ A) {f : V ⟶ X} {g : V ⟶ Y} (p : X ⟶ Y) (h : f ≫ p = g) {T : DiagSet.{u}}
    (t : T ⟶ relativeMappingSpace i f) :
    (relativeMappingSpaceHomEquiv i g T (t ≫ relativeMappingSpaceMapOfEq i p h)).1 =
      (relativeMappingSpaceHomEquiv i f T t).1 ≫ p := by
  dsimp only [relativeMappingSpaceHomEquiv, Equiv.coe_fn_mk]
  rw [Category.assoc, relativeMappingSpaceMapOfEq_fst, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm]

section Square

variable {V A V' A' X : DiagSet.{u}} {i : V ⟶ A} {i' : V' ⟶ A'} (a : A' ⟶ A) (b : V' ⟶ V)
  (w : i' ≫ a = b ≫ i) {f : V ⟶ X} {f' : V' ⟶ X} (hf : f' = b ≫ f)

noncomputable def relativeMappingSpaceMapOfSquare :
    relativeMappingSpace i f ⟶ relativeMappingSpace i' f' :=
  (relativeMappingSpaceHomEquiv i' f' _).symm
    ⟨(grayTensorLeft _).map a ≫ (relativeMappingSpaceHomEquiv i f _ (𝟙 _)).1, by
      rw [← Category.assoc, ← Functor.map_comp, w, Functor.map_comp, Category.assoc,
        (relativeMappingSpaceHomEquiv i f _ (𝟙 _)).2, ← Category.assoc,
        grayTensorLeft_map_grayTensorSnd, Category.assoc, hf]⟩

theorem relativeMappingSpaceHomEquiv_relativeMappingSpaceMapOfSquare {T : DiagSet.{u}}
    (t : T ⟶ relativeMappingSpace i f) :
    (relativeMappingSpaceHomEquiv i' f' T (t ≫ relativeMappingSpaceMapOfSquare a b w hf)).1 =
      (grayTensorLeft T).map a ≫ (relativeMappingSpaceHomEquiv i f T t).1 := by
  have h : (relativeMappingSpaceHomEquiv i' f' _ (relativeMappingSpaceMapOfSquare a b w hf)).1 =
      (grayTensorLeft _).map a ≫ (relativeMappingSpaceHomEquiv i f _ (𝟙 _)).1 :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  rw [relativeMappingSpaceHomEquiv_comp, h, ← Category.assoc,
    ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc,
    ← relativeMappingSpaceHomEquiv_comp, Category.comp_id]

end Square

noncomputable def DiagSet.mappingSpaceIsoRelativeMappingSpace {X : DiagSet.{u}}
    (x y : X.Vertex) :
    (X.mappingSpace x y).toFunctor ≅
      relativeMappingSpace intervalBoundaryι (coprod.desc (vertexHom x) (vertexHom y)) :=
  Yoneda.ext _ _
    (fun {T} t => (relativeMappingSpaceHomEquiv _ _ T).symm
      ⟨(X.mappingSpaceHomEquiv x y T t).1,
        (isFixedEnds_iff_restrict x y _).1 (X.mappingSpaceHomEquiv x y T t).2⟩)
    (fun {T} t => (X.mappingSpaceHomEquiv x y T).symm
      ⟨(relativeMappingSpaceHomEquiv _ _ T t).1,
        (isFixedEnds_iff_restrict x y _).2 (relativeMappingSpaceHomEquiv _ _ T t).2⟩)
    (fun {T} t => (X.mappingSpaceHomEquiv x y T).injective (Subtype.ext (by
      rw [Equiv.apply_symm_apply]
      dsimp only
      rw [Equiv.apply_symm_apply])))
    (fun {T} t => (relativeMappingSpaceHomEquiv _ _ T).injective (Subtype.ext (by
      rw [Equiv.apply_symm_apply]
      dsimp only
      rw [Equiv.apply_symm_apply])))
    (fun {T T'} g t => (relativeMappingSpaceHomEquiv _ _ T').injective (Subtype.ext (by
      rw [Equiv.apply_symm_apply]
      dsimp only
      rw [relativeMappingSpaceHomEquiv_comp, DiagSet.mappingSpaceHomEquiv_comp,
        Equiv.apply_symm_apply])))

theorem DiagSet.relativeMappingSpaceHomEquiv_mappingSpaceIsoRelativeMappingSpace
    {X : DiagSet.{u}} (x y : X.Vertex) {T : DiagSet.{u}}
    (t : T ⟶ (X.mappingSpace x y).toFunctor) :
    (relativeMappingSpaceHomEquiv _ _ T
        (t ≫ (DiagSet.mappingSpaceIsoRelativeMappingSpace x y).hom)).1 =
      (X.mappingSpaceHomEquiv x y T t).1 := by
  have h : (relativeMappingSpaceHomEquiv _ _ _
      (DiagSet.mappingSpaceIsoRelativeMappingSpace (X := X) x y).hom).1 =
      (X.mappingSpaceHomEquiv x y _ (𝟙 _)).1 :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  rw [relativeMappingSpaceHomEquiv_comp, h, ← DiagSet.mappingSpaceHomEquiv_comp, Category.comp_id]

private theorem exists_app_eq_of_comp {V A' A : DiagSet.{u}} (j : V ⟶ A') (k : A' ⟶ A) [Mono k]
    (hi : ∀ a : A.Vertex, ∃ v : V.Vertex, v.map (j ≫ k) = a)
    (a : A'.Vertex) : ∃ v : V.Vertex, v.map j = a := by
  obtain ⟨v, hv⟩ := hi (a.map k)
  exact ⟨v, (mono_iff_injective (k.app _)).1 inferInstance hv⟩

theorem fibration_toInfty_zero_relativeMappingSpaceRestrict {V A' A X : DiagSet.{u}}
    (j : V ⟶ A') (k : A' ⟶ A) [Mono j] [Mono k]
    (hi : ∀ a : A.Vertex, ∃ v : V.Vertex, v.map (j ≫ k) = a)
    (f : V ⟶ X) (hX : IsInftyCategory 1 X) :
    Fibration ((DiagSet.toInfty 0).map (relativeMappingSpaceRestrict j k f)) := by
  have := fibration_toInfty_one_grayHomRestrict k hX
  have : Fibration ((DiagSet.toInfty 1).map (relativeMappingSpaceRestrict j k f)) :=
    (fibration_iff _).2 ((fibrations (DiagSet.Infty.{u} 1)).of_isPullback
      (isPullback_relativeMappingSpaceRestrict j k f) ((fibration_iff _).1 this))
  exact DiagSet.Infty.fibration_of_le zero_le_one _
    (isInftyCategory_zero_relativeMappingSpace (j ≫ k) hi f hX)
    (isInftyCategory_zero_relativeMappingSpace j (exists_app_eq_of_comp j k hi) f hX)

private noncomputable def isTerminalGrayHomRightTerminal (K : DiagSet.{u}) :
    IsTerminal ((grayHomRight K).obj (⊤_ DiagSet.{u})) :=
  have := (grayTensorRightAdjunction K).rightAdjoint_preservesLimits
  terminalIsTerminal.isTerminalObj (grayHomRight K) _

private theorem rlp_monomorphisms_grayHomRestrict {A' A X : DiagSet.{u}} (k : A' ⟶ A) [Mono k]
    [WeakEquivalence ((DiagSet.toInfty 1).map k)] (hX : IsInftyCategory 1 X) :
    (monomorphisms DiagSet.{u}).rlp ((grayHomRestrict k).app X) := by
  have : Fibration ((DiagSet.toInfty 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 ((isFibrant_infty_iff 1 _).2 hX)
  let sq := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} k (terminal.from X)
  have hfst : IsIso sq.fst := sq.isPullback.isIso_fst_of_isIso
    (isIso_of_isTerminal (isTerminalGrayHomRightTerminal A) (isTerminalGrayHomRightTerminal A') _)
  have := fibration_toInfty_one_grayHomRight_pullbackObjObj k (terminal.from X)
  have := weakEquivalence_toInfty_one_grayHomRight_pullbackObjObj k (terminal.from X)
    (Or.inl inferInstance)
  have hπ := rlp_monomorphisms_of_trivialFibration_toInfty_map 1 (g := sq.π)
  have e : sq.π ≫ sq.fst = (grayHomRestrict k).app X := sq.π_fst
  rw [← e]
  exact (monomorphisms DiagSet.{u}).rlp.comp_mem _ _ hπ fun _ _ i _ =>
    @HasLiftingProperty.of_right_iso _ _ _ _ _ _ sq.fst i hfst

theorem rlp_monomorphisms_relativeMappingSpaceRestrict {V A' A X : DiagSet.{u}}
    (j : V ⟶ A') (k : A' ⟶ A) [Mono k]
    [WeakEquivalence ((DiagSet.toInfty 1).map k)] (f : V ⟶ X) (hX : IsInftyCategory 1 X) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (relativeMappingSpaceRestrict j k f) :=
  (monomorphisms DiagSet.{u}).rlp.of_isPullback (isPullback_relativeMappingSpaceRestrict j k f)
    (rlp_monomorphisms_grayHomRestrict k hX)

private theorem fibration_toInfty_zero_relativeMappingSpaceMapOfEq {V A X Y : DiagSet.{u}}
    (i : V ⟶ A) [Mono i]
    (hi : ∀ a : A.Vertex, ∃ v : V.Vertex, v.map i = a)
    {f : V ⟶ X} {g : V ⟶ Y} (p : X ⟶ Y) (h : f ≫ p = g) [Fibration ((DiagSet.toInfty 1).map p)]
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) :
    Fibration ((DiagSet.toInfty 0).map (relativeMappingSpaceMapOfEq i p h)) := by
  have := fibration_toInfty_one_grayHomRight_pullbackObjObj i p
  have : Fibration ((DiagSet.toInfty 1).map (relativeMappingSpaceMapOfEq i p h)) :=
    (fibration_iff _).2 ((fibrations (DiagSet.Infty.{u} 1)).of_isPullback
      (isPullback_relativeMappingSpaceMapOfEq i p h) ((fibration_iff _).1 this))
  exact DiagSet.Infty.fibration_of_le zero_le_one _
    (isInftyCategory_zero_relativeMappingSpace i hi f hX)
    (isInftyCategory_zero_relativeMappingSpace i hi g hY)

theorem fibration_toInfty_zero_relativeMappingSpaceMap {V A X Y : DiagSet.{u}} (i : V ⟶ A)
    [Mono i] (hi : ∀ a : A.Vertex, ∃ v : V.Vertex, v.map i = a)
    (f : V ⟶ X) (p : X ⟶ Y) [Fibration ((DiagSet.toInfty 1).map p)]
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) :
    Fibration ((DiagSet.toInfty 0).map (relativeMappingSpaceMap i f p)) :=
  fibration_toInfty_zero_relativeMappingSpaceMapOfEq i hi p rfl hX hY

theorem rlp_monomorphisms_relativeMappingSpaceMap {V A X Y : DiagSet.{u}} (i : V ⟶ A) [Mono i]
    (f : V ⟶ X) {p : X ⟶ Y} (hp : (MorphismProperty.monomorphisms DiagSet.{u}).rlp p) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (relativeMappingSpaceMap i f p) := by
  refine (monomorphisms DiagSet.{u}).rlp.of_isPullback
    (isPullback_relativeMappingSpaceMapOfEq i p rfl) fun K L j hj => ?_
  exact rlp_monomorphisms_grayHomRight_pullbackObjObj i hp j hj

noncomputable def relativeCylinder {V A : DiagSet.{u}} (i : V ⟶ A) : DiagSet.{u} ⥤ Under V where
  obj T := Under.mk (pushout.inr ((grayTensorLeft T).map i) (grayTensorSnd T V))
  map {T T'} g := CategoryTheory.Under.homMk (U := Under.mk _) (V := Under.mk _)
    (pushout.map _ _ _ _ ((grayTensorRight A).map g)
      (𝟙 V) ((grayTensorRight V).map g) (grayTensorLeft_map_comp_grayTensorRight_map g i)
      (by rw [Category.comp_id, grayTensorRight_map_grayTensorSnd]))
    ((pushout.inr_desc _ _ _).trans (Category.id_comp _))
  map_id T := Under.UnderMorphism.ext (pushout.hom_ext
    (by
      simp only [Under.homMk_right, Under.id_right, pushout.map, pushout.inl_desc,
        CategoryTheory.Functor.map_id, Under.mk_right, Category.comp_id]
      exact Category.id_comp _)
    (by simp only [Under.homMk_right, Under.id_right, pushout.map, pushout.inr_desc,
      Category.id_comp, Under.mk_right, Category.comp_id]))
  map_comp f g := Under.UnderMorphism.ext (pushout.hom_ext
    (by simp only [Under.homMk_right, Under.comp_right, pushout.map, pushout.inl_desc,
      pushout.inl_desc_assoc, CategoryTheory.Functor.map_comp, Category.assoc])
    (by simp only [Under.homMk_right, Under.comp_right, pushout.map, pushout.inr_desc,
      pushout.inr_desc_assoc, Category.id_comp]))

noncomputable def relativeMappingSpaceFunctor {V A : DiagSet.{u}} (i : V ⟶ A) :
    Under V ⥤ DiagSet.{u} where
  obj Y := relativeMappingSpace i Y.hom
  map φ := relativeMappingSpaceMapOfEq i φ.right (Under.w φ)
  map_id Y := pullback.hom_ext
    (by simp only [relativeMappingSpaceMapOfEq, pullback.map, pullback.lift_fst, Under.id_right,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp])
    (by simp only [relativeMappingSpaceMapOfEq, pullback.map, pullback.lift_snd,
      Category.comp_id, Category.id_comp])
  map_comp φ ψ := pullback.hom_ext
    (by simp only [relativeMappingSpaceMapOfEq, pullback.map, pullback.lift_fst,
      pullback.lift_fst_assoc, Under.comp_right, CategoryTheory.Functor.map_comp, Category.assoc])
    (by simp only [relativeMappingSpaceMapOfEq, pullback.map, pullback.lift_snd, Category.assoc,
      Category.comp_id])

@[reassoc]
theorem inl_relativeCylinder_map_right {V A : DiagSet.{u}} (i : V ⟶ A) {T T' : DiagSet.{u}}
    (g : T ⟶ T') :
    pushout.inl ((grayTensorLeft T).map i) (grayTensorSnd T V) ≫
        ((relativeCylinder i).map g).right =
      (grayTensorRight A).map g ≫ pushout.inl ((grayTensorLeft T').map i) (grayTensorSnd T' V) :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem inr_relativeCylinder_map_right {V A : DiagSet.{u}} (i : V ⟶ A) {T T' : DiagSet.{u}}
    (g : T ⟶ T') :
    pushout.inr ((grayTensorLeft T).map i) (grayTensorSnd T V) ≫
        ((relativeCylinder i).map g).right =
      pushout.inr ((grayTensorLeft T').map i) (grayTensorSnd T' V) :=
  (pushout.inr_desc _ _ _).trans (Category.id_comp _)

private noncomputable def relativeCylinderHomEquiv {V A : DiagSet.{u}} (i : V ⟶ A)
    (T : DiagSet.{u}) (Y : Under V) : ((relativeCylinder i).obj T ⟶ Y) ≃
      {F : grayTensor T A ⟶ Y.right //
        (grayTensorLeft T).map i ≫ F = grayTensorSnd T V ≫ Y.hom} where
  toFun φ := ⟨pushout.inl _ _ ≫ φ.right, (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ φ.right) pushout.condition).trans
      ((Category.assoc _ _ _).trans (congrArg _ (Under.w φ))))⟩
  invFun F := CategoryTheory.Under.homMk (U := Under.mk _) (pushout.desc F.1 Y.hom F.2)
    (pushout.inr_desc _ _ _)
  left_inv φ := Under.UnderMorphism.ext (pushout.hom_ext (pushout.inl_desc _ _ _)
    ((pushout.inr_desc _ _ _).trans (Under.w φ).symm))
  right_inv _ := Subtype.ext (pushout.inl_desc _ _ _)

noncomputable def relativeCylinderAdjunction {V A : DiagSet.{u}} (i : V ⟶ A) :
    relativeCylinder i ⊣ relativeMappingSpaceFunctor i :=
  Adjunction.mkOfHomEquiv
    { homEquiv T Y := (relativeCylinderHomEquiv i T Y).trans
        (relativeMappingSpaceHomEquiv i Y.hom T).symm
      homEquiv_naturality_left_symm g φ := Under.UnderMorphism.ext (pushout.hom_ext
        ((pushout.inl_desc _ _ _).trans <|
          (congrArg _ (Category.assoc g φ _)).trans <|
          ((grayTensorRightAdjunction A).homEquiv_naturality_left_symm _ _).trans <|
          (congrArg _ (pushout.inl_desc _ _ _).symm).trans <|
          (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ _) (inl_relativeCylinder_map_right i g).symm).trans (Category.assoc _ _ _))
        ((pushout.inr_desc _ _ _).trans <| (pushout.inr_desc _ _ _).symm.trans <|
          (congrArg (· ≫ _) (inr_relativeCylinder_map_right i g).symm).trans
            (Category.assoc _ _ _)))
      homEquiv_naturality_right _ ψ := pullback.hom_ext
        ((pullback.lift_fst _ _ _).trans <|
          (congrArg _ (Category.assoc _ _ _).symm).trans <|
          ((grayTensorRightAdjunction A).homEquiv_naturality_right _ _).trans <|
          (congrArg (· ≫ _) (pullback.lift_fst _ _ _).symm).trans <|
          (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (relativeMappingSpaceMapOfEq_fst i ψ.right (Under.w ψ)).symm).trans
            (Category.assoc _ _ _).symm)
        (isTerminalBallAtomPoint.hom_ext _ _) }

theorem mono_relativeCylinder_map_right {V A : DiagSet.{u}} (i : V ⟶ A) [Mono i]
    {T T' : DiagSet.{u}} (g : T ⟶ T') [Mono g] : Mono ((relativeCylinder i).map g).right := by
  have hQ := IsPushout.of_hasPushout ((grayTensorRight V).map g) ((grayTensorLeft T).map i)
  let ι : pushout ((grayTensorRight V).map g) ((grayTensorLeft T).map i) ⟶ grayTensor T' A :=
    pushout.desc ((grayTensorLeft T').map i) ((grayTensorRight A).map g)
      (grayTensorLeft_map_comp_grayTensorRight_map g i).symm
  have : Mono ι := mono_pushoutProduct g i
  let c : pushout ((grayTensorRight V).map g) ((grayTensorLeft T).map i) ⟶
      pushout ((grayTensorLeft T).map i) (grayTensorSnd T V) :=
    pushout.desc (grayTensorSnd T' V ≫ pushout.inr _ _) (pushout.inl _ _) (by
      rw [← Category.assoc, grayTensorRight_map_grayTensorSnd, pushout.condition])
  let Cg : pushout ((grayTensorLeft T).map i) (grayTensorSnd T V) ⟶
      pushout ((grayTensorLeft T').map i) (grayTensorSnd T' V) := ((relativeCylinder i).map g).right
  have eι₁ : pushout.inl _ _ ≫ ι = (grayTensorLeft T').map i := pushout.inl_desc _ _ _
  have eι₂ : pushout.inr _ _ ≫ ι = (grayTensorRight A).map g := pushout.inr_desc _ _ _
  have ec₁ : pushout.inl _ _ ≫ c = grayTensorSnd T' V ≫ pushout.inr _ _ := pushout.inl_desc _ _ _
  have ec₂ : pushout.inr _ _ ≫ c = pushout.inl _ _ := pushout.inr_desc _ _ _
  have eC₁ : pushout.inl _ _ ≫ Cg = (grayTensorRight A).map g ≫ pushout.inl _ _ :=
    inl_relativeCylinder_map_right i g
  have eC₂ : pushout.inr _ _ ≫ Cg = pushout.inr _ _ := inr_relativeCylinder_map_right i g
  have h₁ : IsPushout (grayTensorSnd T' V) (pushout.inl _ _) (pushout.inr _ _) c := by
    refine IsPushout.of_left ?_ ec₁.symm hQ
    rw [grayTensorRight_map_grayTensorSnd, ec₂]
    exact (IsPushout.of_hasPushout _ _).flip
  have h₂ : IsPushout ι c (pushout.inl ((grayTensorLeft T').map i) (grayTensorSnd T' V)) Cg := by
    refine IsPushout.of_left ?_ ?_ h₁.flip
    · rw [eι₁, eC₂]
      exact IsPushout.of_hasPushout _ _
    · refine pushout.hom_ext ?_ ?_
      · rw [reassoc_of% eι₁, reassoc_of% ec₁, eC₂, pushout.condition]
      · rw [reassoc_of% eι₂, reassoc_of% ec₂, eC₁]
  exact (monomorphisms DiagSet.{u}).of_isPushout h₂.flip (monomorphisms.infer_property ι)

noncomputable def relativeCylinderInfty {V A : DiagSet.{u}} (i : V ⟶ A) :
    DiagSet.Infty.{u} 0 ⥤ Under ((DiagSet.toInfty 1).obj V) :=
  relativeCylinder i

noncomputable def relativeMappingSpaceInfty {V A : DiagSet.{u}} (i : V ⟶ A) :
    Under ((DiagSet.toInfty 1).obj V) ⥤ DiagSet.Infty.{u} 0 :=
  relativeMappingSpaceFunctor i

noncomputable def relativeCylinderAdjunctionInfty {V A : DiagSet.{u}} (i : V ⟶ A) :
    relativeCylinderInfty i ⊣ relativeMappingSpaceInfty i :=
  relativeCylinderAdjunction i

theorem isQuillen_relativeCylinderAdjunctionInfty {V A : DiagSet.{u}} (i : V ⟶ A) [Mono i]
    (hi : ∀ a : A.Vertex, ∃ v : V.Vertex, v.map i = a) :
    (relativeCylinderAdjunctionInfty i).IsQuillen := by
  refine (relativeCylinderAdjunctionInfty i).isQuillen_of_fibrations_between_fibrant
    (fun _ _ g hg => (cofibration_iff _).1 ((cofibrations_under_iff _ _).2
      ((cofibration_iff _).2 (@mono_relativeCylinder_map_right _ _ i _ _ _ g hg))))
    fun X Y p hX hY hp => ?_
  have hX' : IsInftyCategory 1 (X.right : DiagSet.{u}) :=
    (isFibrant_infty_iff 1 X.right).1 ((isFibrant_under_iff _ X).1 hX)
  have hY' : IsInftyCategory 1 (Y.right : DiagSet.{u}) :=
    (isFibrant_infty_iff 1 Y.right).1 ((isFibrant_under_iff _ Y).1 hY)
  have : Fibration ((DiagSet.toInfty 1).map p.right) := (fibrations_under_iff _ p).1 hp
  exact fibration_toInfty_zero_relativeMappingSpaceMapOfEq i hi p.right (Under.w p) hX' hY'

theorem weakEquivalence_relativeMappingSpaceMapOfEq {V A X Y : DiagSet.{u}}
    (i : V ⟶ A) [Mono i]
    (hi : ∀ a : A.Vertex, ∃ v : V.Vertex, v.map i = a)
    {f : V ⟶ X} {g : V ⟶ Y} (p : X ⟶ Y) (h : f ≫ p = g)
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    [WeakEquivalence ((DiagSet.toInfty 1).map p)] :
    WeakEquivalence ((DiagSet.toInfty 0).map (relativeMappingSpaceMapOfEq i p h)) := by
  let f' : Under ((DiagSet.toInfty 1).obj V) := Under.mk f
  let g' : Under ((DiagSet.toInfty 1).obj V) := Under.mk g
  let p' : f' ⟶ g' := Under.homMk p h
  have : IsFibrant f' := (isFibrant_under_iff _ _).2 ((isFibrant_infty_iff 1 _).2 hX)
  have : IsFibrant g' := (isFibrant_under_iff _ _).2 ((isFibrant_infty_iff 1 _).2 hY)
  have : WeakEquivalence p' := (weakEquivalences_under_iff _ _).2
    ‹WeakEquivalence ((DiagSet.toInfty 1).map p)›
  exact (isQuillen_relativeCylinderAdjunctionInfty i hi).weakEquivalence_map_of_isFibrant p'

theorem weakEquivalence_toInfty_one_relativeMappingSpaceMapOfEq {V A X Y : DiagSet.{u}}
    (i : V ⟶ A) [Mono i] {f : V ⟶ X} {g : V ⟶ Y} (p : X ⟶ Y) (h : f ≫ p = g)
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    [WeakEquivalence ((DiagSet.toInfty 1).map p)] :
    WeakEquivalence ((DiagSet.toInfty 1).map (relativeMappingSpaceMapOfEq i p h)) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 X).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 Y).2 hY
  have := fibration_toInfty_one_grayHomRestrict i hX
  have := fibration_toInfty_one_grayHomRestrict i hY
  have : IsFibrant ((DiagSet.toInfty 1).obj ((grayHomRight V).obj X)) :=
    (isFibrant_infty_iff 1 _).2 (isInftyCategory_grayHomRight _ hX)
  have : IsFibrant ((DiagSet.toInfty 1).obj ((grayHomRight V).obj Y)) :=
    (isFibrant_infty_iff 1 _).2 (isInftyCategory_grayHomRight _ hY)
  have : PreservesLimits (DiagSet.toInfty 1) :=
    inferInstanceAs (PreservesLimits (𝟭 DiagSet.{u}))
  have : IsFibrant ((DiagSet.toInfty 1).obj (ball.{u} atomPoint)) :=
    (isFibrant_iff_of_isTerminal (𝟙 _)
      (isTerminalBallAtomPoint.isTerminalObj (DiagSet.toInfty 1) _)).2 inferInstance
  have : WeakEquivalence ((DiagSet.toInfty 1).map ((grayHomRight A).map p)) :=
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one A).weakEquivalence_map_of_isFibrant
      ((DiagSet.toInfty 1).map p)
  have : WeakEquivalence ((DiagSet.toInfty 1).map ((grayHomRight V).map p)) :=
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one V).weakEquivalence_map_of_isFibrant
      ((DiagSet.toInfty 1).map p)
  exact ((DiagSet.toInfty 1).map_isPullback (IsPullback.of_hasPullback
      ((grayHomRestrict i).app X) (diagramPoint f))).weakEquivalence_map_of_fibration
    ((DiagSet.toInfty 1).map_isPullback (IsPullback.of_hasPullback
      ((grayHomRestrict i).app Y) (diagramPoint g)))
    ((DiagSet.toInfty 1).map ((grayHomRight A).map p))
    ((DiagSet.toInfty 1).map ((grayHomRight V).map p)) (𝟙 _)
    ((DiagSet.toInfty 1).map (relativeMappingSpaceMapOfEq i p h))
    (by rw [← Functor.map_comp, ← Functor.map_comp, (grayHomRestrict i).naturality])
    (by rw [Category.id_comp, ← Functor.map_comp, diagramPoint_comp, h])
    (by rw [← Functor.map_comp, ← Functor.map_comp, relativeMappingSpaceMapOfEq_fst])
    (by
      rw [Category.comp_id, ← Functor.map_comp]
      exact congrArg (DiagSet.toInfty 1).map (relativeMappingSpaceMapOfEq_snd i p h))

end Atoms.Diagrammatic
