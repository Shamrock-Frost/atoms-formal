import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Monoidal
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Atoms.Homotopical.Simplicial.CartesianInduction

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial MonoidalCategory
open CartesianMonoidalCategory MonoidalCategory.Arrow

universe u

namespace Atoms.Homotopical

open MarkedSSet.modelCategoryCartesian

noncomputable def MarkedSSet.sharpJPoint (ε : Bool) : 𝟙_ MarkedSSet.{u} ⟶ MarkedSSet.sharpJ :=
  ((cartesianEndpoint.{u} ε).app (𝟙_ _) :
    𝟙_ MarkedSSet.{u} ⟶ MarkedSSet.sharpJ.{u} ⨯ 𝟙_ MarkedSSet.{u}) ≫ prod.fst

noncomputable def cartesianCylinderTensorLeftIso :
    cartesianCylinder.{u}.TensorLeftIso MarkedSSet.sharpJ MarkedSSet.sharpJPoint where
  iso := (CartesianMonoidalCategory.tensorLeftIsoProd _).symm
  endpoint_app_comp_iso_hom_app ε X := by
    have h₁ : (CartesianMonoidalCategory.tensorLeftIsoProd MarkedSSet.sharpJ.{u}).inv.app X ≫
        fst _ X = prod.fst :=
      IsLimit.conePointUniqueUpToIso_inv_comp (tensorProductIsBinaryProduct _ X)
        (limit.isLimit _) (Discrete.mk WalkingPair.left)
    have h₂ : (CartesianMonoidalCategory.tensorLeftIsoProd MarkedSSet.sharpJ.{u}).inv.app X ≫
        snd _ X = prod.snd :=
      IsLimit.conePointUniqueUpToIso_inv_comp (tensorProductIsBinaryProduct _ X)
        (limit.isLimit _) (Discrete.mk WalkingPair.right)
    have hn : toUnit X ≫ (cartesianEndpoint.{u} ε).app (𝟙_ _) =
        (cartesianEndpoint.{u} ε).app X ≫ prod.map (𝟙 _) (toUnit X) :=
      (cartesianEndpoint.{u} ε).naturality (toUnit X)
    apply CartesianMonoidalCategory.hom_ext
    · refine (congrArg ((cartesianEndpoint.{u} ε).app X ≫ ·) h₁).trans ?_
      simp only [Category.assoc, whiskerRight_fst, MarkedSSet.sharpJPoint]
      have h₃ (φ : X ⟶ MarkedSSet.sharpJ.{u} ⨯ X) :
          (φ ≫ prod.map (𝟙 _) (toUnit X)) ≫ prod.fst = φ ≫ prod.fst := by
        rw [Category.assoc, prod.map_fst, Category.comp_id]
      exact (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ prod.fst) hn)).trans
        (h₃ _)).symm
    · refine (congrArg ((cartesianEndpoint.{u} ε).app X ≫ ·) h₂).trans ?_
      simp only [Category.assoc, whiskerRight_snd]
      exact cartesianCylinder.{u}.endpoint_app_contraction_app ε X

theorem MarkedSSet.mem_marked_tensor_iff (X Y : MarkedSSet.{u})
    (e : (X ⊗ Y).underlying _⦋1⦌) :
    e ∈ (X ⊗ Y).marked ⦋1⦌ ↔ e.1 ∈ X.marked ⦋1⦌ ∧ e.2 ∈ Y.marked ⦋1⦌ := by
  constructor
  · rintro ⟨h, y, rfl⟩
    exact ⟨⟨h, y.1, rfl⟩, ⟨h, y.2, rfl⟩⟩
  · rintro ⟨⟨h, y₁, h₁⟩, ⟨_, y₂, h₂⟩⟩
    exact ⟨h, (y₁, y₂), Prod.ext h₁ h₂⟩

theorem isIso_forget_map_pushoutProduct {A B X Y : MarkedSSet.{u}} (f : A ⟶ B)
    (g : X ⟶ Y)
    (h : IsIso (MarkedPresheaf.forget.map f) ∨ IsIso (MarkedPresheaf.forget.map g)) :
    IsIso (MarkedPresheaf.forget.map (Arrow.mk f □ Arrow.mk g).hom) := by
  let F := MarkedPresheaf.forget (D := edgeMarking)
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u}) f g
  exact h.elim (fun _ => sq.isIso_map_ι_of_left F (inferInstanceAs (IsIso (F.map f ▷ F.obj X)))
      (inferInstanceAs (IsIso (F.map f ▷ F.obj Y)))) fun _ => sq.isIso_map_ι_of_right F
    (inferInstanceAs (IsIso (F.obj A ◁ F.map g))) (inferInstanceAs (IsIso (F.obj B ◁ F.map g)))

private theorem weakEquivalence_pushoutProduct_of_isIso_forget {A B X Y : MarkedSSet.{u}}
    (f : A ⟶ B) (g : X ⟶ Y)
    (hiso : IsIso (MarkedPresheaf.forget.map f) ∨ IsIso (MarkedPresheaf.forget.map g))
    (h : ∀ (F : SSet.{u}) [F.Quasicategory] (φ : MarkedPresheaf.forget.obj (B ⊗ Y) ⟶ F),
      (∀ e ∈ (A ⊗ Y).marked ⦋1⦌, Nonempty (SSet.Edge.mk'
        (φ.app _ ((MarkedPresheaf.forget.map (f ▷ Y)).app _ e))).InvStruct) →
      (∀ e ∈ (B ⊗ X).marked ⦋1⦌, Nonempty (SSet.Edge.mk'
        (φ.app _ ((MarkedPresheaf.forget.map (B ◁ g)).app _ e))).InvStruct) →
      ∀ e ∈ (B ⊗ Y).marked ⦋1⦌, Nonempty (SSet.Edge.mk' (φ.app _ e)).InvStruct) :
    WeakEquivalence (Arrow.mk f □ Arrow.mk g).hom := by
  have hc {F : SSet.{u}} {x y : F _⦋1⦌} (hxy : x = y)
      (hx : Nonempty (SSet.Edge.mk' x).InvStruct) : Nonempty (SSet.Edge.mk' y).InvStruct :=
    hxy ▸ hx
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u}) f g
  have : IsIso (MarkedPresheaf.forget.map sq.ι) := isIso_forget_map_pushoutProduct f g hiso
  refine weakEquivalence_of_isIso_forget_map (B := B ⊗ Y) sq.ι fun F _ φ hφ ↦
    h F φ (fun e he ↦ ?_) (fun e he ↦ ?_)
  · refine hc ?_ (hφ _ (MarkedPresheaf.map_mem_marked sq.inr he))
    exact congrArg (φ.app _) (ConcreteCategory.congr_hom
      (congr_app ((Functor.map_comp _ _ _).symm.trans
        (congrArg MarkedPresheaf.forget.map sq.inr_ι)) _) e)
  · refine hc ?_ (hφ _ (MarkedPresheaf.map_mem_marked sq.inl he))
    exact congrArg (φ.app _) (ConcreteCategory.congr_hom
      (congr_app ((Functor.map_comp _ _ _).symm.trans
        (congrArg MarkedPresheaf.forget.map sq.inl_ι)) _) e)

section Generators

open SSet

theorem trivialCofibrations_pushoutProduct_flat_horn_flat {n : ℕ} (i : Fin (n + 3))
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) {K L : SSet.{u}} (b : K ⟶ L) [Mono b] :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (Arrow.mk ((MarkedPresheaf.flat.{u} edgeMarking).map Λ[n + 2, i].ι) □
        Arrow.mk ((MarkedPresheaf.flat.{u} edgeMarking).map b)).hom := by
  let F := MarkedPresheaf.forget (D := edgeMarking)
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    ((MarkedPresheaf.flat edgeMarking).map Λ[n + 2, i].ι) ((MarkedPresheaf.flat edgeMarking).map b)
  let sq' : (curriedTensor SSet.{u}).PushoutObjObj Λ[n + 2, i].ι b :=
    { pt := F.obj sq.pt
      inl := F.map sq.inl
      inr := F.map sq.inr
      isPushout := sq.isPushout.map F
      ι := F.map sq.ι
      inl_ι := (F.map_comp _ _).symm.trans (congrArg F.map sq.inl_ι)
      inr_ι := (F.map_comp _ _).symm.trans (congrArg F.map sq.inr_ι) }
  have hA : innerAnodyneExtensions sq'.ι :=
    innerAnodyneExtensions_pushoutObjObjι' sq' fun _ _ p hp ↦ hp _ (.intro i h0 hn)
  have : Mono ((MarkedPresheaf.flat edgeMarking).map Λ[n + 2, i].ι) :=
    (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono Λ[n + 2, i].ι))
  have : Mono ((MarkedPresheaf.flat edgeMarking).map b) :=
    (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono b))
  refine ⟨Arrow.mono_pushoutProduct _ _, (weakEquivalence_iff _).1
    (weakEquivalence_of_hasLiftingProperty sq.ι fun E B p hE hB hp ↦ ⟨fun {x y} w ↦ ?_⟩)⟩
  have : SSet.Quasicategory (F.obj E) :=
    ((MarkedSSet.modelCategoryCartesian.isFibrant_iff E).1 hE).1
  have : SSet.Quasicategory (F.obj B) :=
    ((MarkedSSet.modelCategoryCartesian.isFibrant_iff B).1 hB).1
  have : InnerFibration (F.map p) := ((fibration_iff_isofibration p).1 hp).toInnerFibration
  have w' : CommSq (F.map x) sq'.ι (F.map p) (F.map y) :=
    ⟨(F.map_comp _ _).symm.trans ((congrArg F.map w.w).trans (F.map_comp _ _))⟩
  have := hA _ ((innerFibration_iff (F.map p)).1 inferInstance)
  obtain ⟨l⟩ := (this.sq_hasLift w').exists_lift
  refine ⟨⟨⟨edgeHomMk l.l fun e he ↦ ?_, MarkedPresheaf.hom_ext ((F.map_comp _ _).trans l.fac_left),
    MarkedPresheaf.hom_ext ((F.map_comp _ _).trans l.fac_right)⟩⟩⟩
  obtain ⟨he₁, he₂⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ e).1 he
  obtain ⟨x₁, hx₁⟩ := exists_eq_σ_of_mem_marked_flat _ he₁
  obtain ⟨x₂, hx₂⟩ := exists_eq_σ_of_mem_marked_flat _ he₂
  have he' : e = (Δ[n + 2] ⊗ L : SSet.{u}).σ 0 (x₁, x₂) := Prod.ext hx₁ hx₂
  rw [he']
  exact (congrArg (· ∈ E.marked ⦋1⦌) (σ_naturality_apply l.l 0 (x₁, x₂))).mpr
    (E.map_σ_mem_marked _)

theorem trivialCofibrations_pushoutProduct_flat_horn_of_isIso_forget {n : ℕ} (i : Fin (n + 3))
    {X Y : MarkedSSet.{u}} (g : X ⟶ Y) [Mono g]
    [IsIso (MarkedPresheaf.forget.map g)] :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (Arrow.mk ((MarkedPresheaf.flat.{u} edgeMarking).map Λ[n + 2, i].ι) □ Arrow.mk g).hom := by
  have : Mono ((MarkedPresheaf.flat edgeMarking).map Λ[n + 2, i].ι) :=
    (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono Λ[n + 2, i].ι))
  refine ⟨Arrow.mono_pushoutProduct _ _, (weakEquivalence_iff _).1
    (weakEquivalence_pushoutProduct_of_isIso_forget _ g (Or.inr inferInstance)
      fun F _ φ hA _ e he ↦ ?_)⟩
  obtain ⟨he₁, he₂⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ e).1 he
  obtain ⟨v, hv⟩ := exists_eq_σ_of_mem_marked_flat _ he₁
  let v' : (Λ[n + 2, i] : SSet.{u}) _⦋0⦌ := ⟨v, by simp⟩
  refine SSet.nonempty_invStruct_congr ?_ (hA ((Λ[n + 2, i] : SSet.{u}).σ 0 v', e.2)
    ((MarkedSSet.mem_marked_tensor_iff _ _ _).2 ⟨MarkedSSet.map_σ_mem_marked _ _, he₂⟩))
  exact congrArg (φ.app _) (Prod.ext hv.symm rfl)

theorem trivialCofibrations_pushoutProduct_flatSharp {X Y : MarkedSSet.{u}} (g : X ⟶ Y)
    [Mono g] :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (Arrow.mk ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
        ((MarkedPresheaf.flat edgeMarking).obj coherentIso.{u}) :
          (MarkedPresheaf.flat edgeMarking).obj coherentIso.{u} ⟶ MarkedSSet.sharpJ.{u}) □
        Arrow.mk g).hom := by
  have : Mono ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
      ((MarkedPresheaf.flat edgeMarking).obj coherentIso.{u}) :
        (MarkedPresheaf.flat edgeMarking).obj coherentIso.{u} ⟶ MarkedSSet.sharpJ.{u}) :=
    cartesianGenerators_le_monomorphisms.{u} _ cartesianGenerators.flatSharp
  refine ⟨Arrow.mono_pushoutProduct _ _, (weakEquivalence_iff _).1
    (weakEquivalence_pushoutProduct_of_isIso_forget _ _
      (Or.inl (inferInstanceAs (IsIso (𝟙 coherentIso.{u})))) fun F _ φ hA _ e he ↦ ?_)⟩
  obtain ⟨-, he₂⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ e).1 he
  have h₁ := hA (coherentIso.σ 0 coherentIso.x₀, e.2)
    ((MarkedSSet.mem_marked_tensor_iff _ _ _).2 ⟨MarkedSSet.map_σ_mem_marked _ _, he₂⟩)
  change Nonempty (Edge.mk' (φ.app _ (coherentIso.σ 0 coherentIso.x₀, e.2))).InvStruct at h₁
  exact nonempty_invStruct_app_prod (Z := F) (C := Y.underlying) φ false e.2 h₁ e.1

private noncomputable def sharpEdgeProdIso :
    sharpEdgeProd.{u} ≅ tensorLeft ((MarkedPresheaf.sharp.{u} edgeMarking).obj Δ[1]) :=
  NatIso.ofComponents (fun X ↦
    { hom := edgeHomMk (Y := (MarkedPresheaf.sharp edgeMarking).obj Δ[1] ⊗ X) (𝟙 _)
        fun e he ↦ (MarkedSSet.mem_marked_tensor_iff
          ((MarkedPresheaf.sharp edgeMarking).obj Δ[1]) X e).2
          ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl, (mem_marked_sharpEdgeProdObj X e).1 he⟩
      inv := edgeHomMk (X := (MarkedPresheaf.sharp edgeMarking).obj Δ[1] ⊗ X) (𝟙 _)
        fun e he ↦ (mem_marked_sharpEdgeProdObj X e).2
          ((MarkedSSet.mem_marked_tensor_iff ((MarkedPresheaf.sharp edgeMarking).obj Δ[1]) X e).1
            he).2
      hom_inv_id := MarkedPresheaf.hom_ext rfl
      inv_hom_id := MarkedPresheaf.hom_ext rfl }) fun _ ↦ MarkedPresheaf.hom_ext rfl

private noncomputable def sharpEdgeVertex :
    𝟙_ MarkedSSet.{u} ⟶ (MarkedPresheaf.sharp edgeMarking).obj Δ[1] :=
  edgeHomMk (SSet.const (stdSimplex.obj₀Equiv.symm 0)) fun _ _ ↦
    (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl

private theorem sharpEdgeVertex_comp :
    sharpEdgeVertex.{u} ≫ (MarkedPresheaf.sharp edgeMarking).map
      (yonedaEquiv.symm coherentIso.hom.edge) = MarkedSSet.sharpJPoint false := by
  refine MarkedPresheaf.hom_ext ?_
  have h₁ := congr_app (whiskerRight_endpoint_forget_comp_cartesianCylinderForgetIso_hom.{u} false)
    (𝟙_ MarkedSSet.{u})
  have e : cartesianCylinderForgetIso.{u}.hom.app (𝟙_ MarkedSSet.{u}) ≫ fst _ _ =
      MarkedPresheaf.forget.map prod.fst :=
    CartesianMonoidalCategory.lift_fst _ _
  have h₂ : MarkedPresheaf.forget.map (MarkedSSet.sharpJPoint.{u} false) =
      (joyalInterval.{u}.cylinder.endpoint false).app (MarkedPresheaf.forget.obj (𝟙_ _)) ≫
        fst _ _ :=
    (Functor.map_comp _ _ _).trans ((congrArg _ e.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ fst _ _) h₁)))
  rw [h₂]
  ext n x
  apply coherentIso.simplexEquiv.injective
  funext j
  rfl

theorem trivialCofibrations_pushoutProduct_sharpHom {X Y : MarkedSSet.{u}} (g : X ⟶ Y)
    [Mono g] :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (Arrow.mk ((MarkedPresheaf.sharp.{u} edgeMarking).map
        (yonedaEquiv.symm coherentIso.hom.edge)) □ Arrow.mk g).hom := by
  have : Mono ((MarkedPresheaf.sharp.{u} edgeMarking).map
      (yonedaEquiv.symm coherentIso.hom.edge)) :=
    cartesianGenerators_le_monomorphisms.{u} _ cartesianGenerators.sharpHom
  refine cartesianCylinder.trivialCofibrations_pushoutProduct_of_comp cartesianGenerators
    cartesianGenerators_le_monomorphisms sharpEdgeVertex _ g ?_ ?_
  · rw [sharpEdgeVertex_comp]
    exact ((cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).arrow_mk_iso_iff
      (cartesianCylinderTensorLeftIso.endpointBoxArrowIso false g)).1
        ⟨cartesianCylinder.{u}.mono_endpointBox false g inferInstance,
          cartesianCylinder.{u}.anodyne_le_weakEquivalences _ cartesianGenerators_le_monomorphisms _
            ((cartesianCylinder.{u}.isAnodyneClass_anodyne cartesianGenerators).endpointBox_mem
              false g inferInstance)⟩
  · refine ((cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).arrow_mk_iso_iff
      (NatTrans.leibnizBoxArrowIso (sharpEdgeEndpoint.{u} 0) sharpEdgeVertex
        (leftUnitorNatIso MarkedSSet.{u}).symm sharpEdgeProdIso (fun X ↦ ?_) g)).1
          (trivialCofibrations_leibnizBox_sharpEdgeEndpoint g)
    have h : CartesianMonoidalCategory.lift
        (SSet.const (stdSimplex.obj₀Equiv.symm 0 : (Δ[1] : SSet.{u}) _⦋0⦌)) (𝟙 X.underlying) =
        (λ_ X.underlying).inv ≫
          SSet.const (stdSimplex.obj₀Equiv.symm 0 : (Δ[1] : SSet.{u}) _⦋0⦌) ▷ X.underlying := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    exact MarkedPresheaf.hom_ext h

private theorem trivialCofibrations_pushoutProduct_generators ⦃A B X Y : MarkedSSet.{u}⦄
    (s : A ⟶ B) (g : X ⟶ Y) (hs : cartesianGenerators s)
    (hg : (functorImage (MarkedPresheaf.flat.{u} edgeMarking) SSet.modelCategoryQuillen.I ⊔
      MarkedPresheaf.markingMaps.{u} edgeMarking) g) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (Arrow.mk s □ Arrow.mk g).hom := by
  rcases hg with ⟨K, L, t, ht, e⟩ | ⟨a, h⟩
  · refine ((cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).arrow_mk_iso_iff
      ((pushoutProduct.obj (Arrow.mk s)).mapIso (eqToIso e))).1 ?_
    have : Mono t := SSet.modelCategoryQuillen.I_le_monomorphisms _ ht
    have : Mono ((MarkedPresheaf.flat.{u} edgeMarking).map t) :=
      (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono t))
    rcases hs with ⟨i, h0, hn⟩ | _ | _
    · exact trivialCofibrations_pushoutProduct_flat_horn_flat i h0 hn t
    · exact trivialCofibrations_pushoutProduct_flatSharp ((MarkedPresheaf.flat edgeMarking).map t)
    · exact trivialCofibrations_pushoutProduct_sharpHom ((MarkedPresheaf.flat edgeMarking).map t)
  · rcases hs with ⟨i, h0, hn⟩ | _ | _
    · exact trivialCofibrations_pushoutProduct_flat_horn_of_isIso_forget i _
    · exact trivialCofibrations_pushoutProduct_flatSharp _
    · exact trivialCofibrations_pushoutProduct_sharpHom _

end Generators

private theorem trivialCofibrations_pushoutProduct {A B X Y : MarkedSSet.{u}} (f : A ⟶ B)
    (hf : cartesianCylinder.{u}.trivialCofibrations cartesianGenerators f) (g : X ⟶ Y) [Mono g] :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators (Arrow.mk f □ Arrow.mk g).hom :=
  cartesianCylinder.trivialCofibrations_pushoutProduct cartesianGenerators
    cartesianGenerators_le_monomorphisms cartesianCylinderTensorLeftIso _
    (MarkedPresheaf.saturation_functorImage_flat_sup_markingMaps edgeMarking
      saturation_I_eq_monomorphisms).ge trivialCofibrations_pushoutProduct_generators f hf g

theorem MarkedSSet.mono_pushoutProduct (f g : Arrow MarkedSSet.{u}) [Mono f.hom] [Mono g.hom] :
    Mono (f □ g).hom :=
  Arrow.mono_pushoutProduct f.hom g.hom

theorem MarkedSSet.weakEquivalence_pushoutProduct (f g : Arrow MarkedSSet.{u}) [Mono f.hom]
    [Mono g.hom] (h : WeakEquivalence f.hom ∨ WeakEquivalence g.hom) :
    WeakEquivalence (f □ g).hom := by
  rw [weakEquivalence_iff]
  rcases h with hf | hg
  · exact (trivialCofibrations_pushoutProduct f.hom ⟨inferInstance, (weakEquivalence_iff _).1 hf⟩
      g.hom).2
  · exact (((cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).arrow_mk_iso_iff
      (PushoutProduct.braiding g f)).1 (trivialCofibrations_pushoutProduct g.hom
        ⟨inferInstance, (weakEquivalence_iff _).1 hg⟩ f.hom)).2

theorem MarkedSSet.isQuillen_ihomAdjunction (Z : MarkedSSet.{u}) :
    (ihom.adjunction Z).IsQuillen := by
  have e {K L : MarkedSSet.{u}} (i : K ⟶ L) :
      (initialIsInitial.to Z □ Arrow.mk i) ≅ Arrow.mk (Z ◁ i) :=
    PushoutProduct.isInitialIso' (Arrow.mk i) initialIsInitial
  refine ⟨fun K L i hi ↦ ?_, fun K L i hi ↦ ?_⟩
  · have : Mono i := hi
    have : Mono (initialIsInitial.to Z) := initial.mono_from _ _
    exact ((monomorphisms _).arrow_mk_iso_iff (e i)).1 (Arrow.mono_pushoutProduct _ _)
  · have : Mono i := hi.1
    have : Mono (initialIsInitial.to Z) := initial.mono_from _ _
    exact ((cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).arrow_mk_iso_iff
      (PushoutProduct.braiding _ _ ≪≫ e i)).1 (trivialCofibrations_pushoutProduct i hi _)

theorem MarkedSSet.weakEquivalence_whiskerLeft (Z : MarkedSSet.{u}) {X Y : MarkedSSet.{u}}
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (Z ◁ f) := by
  have (W : MarkedSSet.{u}) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    exact monomorphisms.infer_property _
  exact (MarkedSSet.isQuillen_ihomAdjunction Z).weakEquivalence_map f

theorem MarkedSSet.weakEquivalence_tensorHom {X X' Y Y' : MarkedSSet.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') [WeakEquivalence f] [WeakEquivalence g] : WeakEquivalence (f ⊗ₘ g) := by
  have := MarkedSSet.weakEquivalence_whiskerLeft X g
  have := MarkedSSet.weakEquivalence_whiskerLeft Y' f
  have h : f ▷ Y' = (β_ X Y').hom ≫ Y' ◁ f ≫ (β_ X' Y').inv := by
    rw [← BraidedCategory.braiding_naturality_left_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [tensorHom_def', h]
  infer_instance

end Atoms.Homotopical

namespace SSet

open Atoms.Homotopical

noncomputable def flatTensorIso (X Y : SSet.{u}) :
    (MarkedPresheaf.flat edgeMarking).obj (X ⊗ Y) ≅
      (MarkedPresheaf.flat edgeMarking).obj X ⊗ (MarkedPresheaf.flat edgeMarking).obj Y where
  hom := edgeHomMk (𝟙 (X ⊗ Y)) fun e he ↦ by
    obtain ⟨v, rfl⟩ := exists_eq_σ_of_mem_marked_flat e he
    exact (MarkedSSet.mem_marked_tensor_iff _ _ _).2
      ⟨MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj X) v.1,
        MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj Y) v.2⟩
  inv := edgeHomMk (𝟙 (X ⊗ Y)) fun e he ↦ by
    obtain ⟨h₁, h₂⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ _).1 he
    obtain ⟨x, hx⟩ := exists_eq_σ_of_mem_marked_flat _ h₁
    obtain ⟨y, hy⟩ := exists_eq_σ_of_mem_marked_flat _ h₂
    rw [show e = (X ⊗ Y).σ 0 (x, y) from Prod.ext hx hy]
    exact MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj (X ⊗ Y)) (x, y)
  hom_inv_id := MarkedPresheaf.hom_ext rfl
  inv_hom_id := MarkedPresheaf.hom_ext rfl

namespace modelCategoryJoyal

open MarkedSSet.modelCategoryCartesian

theorem weakEquivalence_whiskerLeft (K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y)
    [WeakEquivalence f] : WeakEquivalence (K ◁ f) := by
  have h : (MarkedPresheaf.flat edgeMarking).map (K ◁ f) = (flatTensorIso K X).hom ≫
      ((MarkedPresheaf.flat edgeMarking).obj K ◁ (MarkedPresheaf.flat edgeMarking).map f) ≫
        (flatTensorIso K Y).inv :=
    MarkedPresheaf.hom_ext rfl
  have := (weakEquivalence_flat_map_iff f).2 inferInstance
  have := MarkedSSet.weakEquivalence_whiskerLeft ((MarkedPresheaf.flat edgeMarking).obj K)
    ((MarkedPresheaf.flat edgeMarking).map f)
  rw [← weakEquivalence_flat_map_iff, h]
  infer_instance

theorem isQuillen_ihomAdjunction (K : SSet.{u}) : (ihom.adjunction K).IsQuillen where
  cofibrations_le _ _ i hi :=
    have : Mono i := hi
    monomorphisms.infer_property (K ◁ i)
  trivialCofibrations_le _ _ i hi :=
    have : Mono i := hi.1
    have : WeakEquivalence i := (weakEquivalence_iff i).2 hi.2
    ⟨monomorphisms.infer_property (K ◁ i),
      (weakEquivalence_iff _).1 (weakEquivalence_whiskerLeft K i)⟩

theorem weakEquivalence_ihom_map (K : SSet.{u}) {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence ((ihom K).map f) :=
  (isQuillen_ihomAdjunction K).weakEquivalence_map_of_isFibrant f

theorem weakEquivalence_tensorHom {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    [WeakEquivalence f] [WeakEquivalence g] : WeakEquivalence (f ⊗ₘ g) := by
  have := weakEquivalence_whiskerLeft X g
  have := weakEquivalence_whiskerLeft Y' f
  have h : f ▷ Y' = (β_ X Y').hom ≫ Y' ◁ f ≫ (β_ X' Y').inv := by
    rw [← BraidedCategory.braiding_naturality_left_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [tensorHom_def', h]
  infer_instance

theorem weakEquivalence_coprodMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    [WeakEquivalence f] [WeakEquivalence g] : WeakEquivalence (coprod.map f g) := by
  have hf : joyalInterval.{u}.cylinder.weakEquivalences innerHornInclusions f :=
    (weakEquivalence_iff f).1 inferInstance
  have hg : joyalInterval.{u}.cylinder.weakEquivalences innerHornInclusions g :=
    (weakEquivalence_iff g).1 inferInstance
  rw [weakEquivalence_iff]
  exact joyalInterval.{u}.cylinder.weakEquivalences_of_isPushout_of_mono
    innerHornInclusions_le_monomorphisms (IsPushout.of_hasBinaryCoproduct' X Y)
    (IsPushout.of_hasBinaryCoproduct' X' Y') (𝟙 _) f g _ (initial.hom_ext _ _)
    (initial.hom_ext _ _) (by simp) (by simp)
    ((weakEquivalence_iff (𝟙 (⊥_ SSet.{u}))).1 inferInstance) hf hg

end modelCategoryJoyal

end SSet
