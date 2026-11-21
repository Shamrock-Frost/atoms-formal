import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.LeftProper
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
import Atoms.Homotopical.Simplicial.CartesianJoyal
import Atoms.Homotopical.Simplicial.Cells
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial

universe u w v₁ u₁

namespace Atoms.Homotopical

open MarkedSSet.modelCategoryCartesian

private theorem isPullback_comp_of_isPushout {K X IK IX B : SSet.{u}} {i : K ⟶ X} [Mono i]
    {e₀ e₁ : K ⟶ IK} {e₀' e₁' : X ⟶ IX} {Ii : IK ⟶ IX} {l : IK ⟶ B} {r : X ⟶ B}
    (hB : IsPushout e₀ i l r) {box : B ⟶ IX} (hl : l ≫ box = Ii) (hr : r ≫ box = e₀')
    (h₁ : IsPullback e₁ i Ii e₁') (hd : ∀ n x y, e₀'.app n x ≠ e₁'.app n y) :
    IsPullback (e₁ ≫ l) i box e₁' := by
  refine IsPullback.of_forall_isPullback_app fun n ↦ (Types.isPullback_iff _ _ _ _).2
    ⟨congr_app (((Category.assoc _ _ _).trans (by rw [hl, h₁.w]) :
      (e₁ ≫ l) ≫ box = i ≫ e₁')) n, fun x y h ↦ ?_, fun β x hβ ↦ ?_⟩
  · exact (mono_iff_injective (i.app n)).1 inferInstance h.2
  · obtain ⟨c, rfl⟩ | ⟨y, rfl⟩ := Types.eq_or_eq_of_isPushout (hB.app n) β
    · obtain ⟨a, ha, rfl⟩ := Types.exists_of_isPullback (h₁.app n) c x (by
        rw [← hβ, ← hl]; rfl)
      exact ⟨a, by rw [← ha]; rfl, rfl⟩
    · exact absurd (by rw [← hβ, ← hr]; rfl) (hd n y x)

private theorem forget_map_endpoint_app_ne (X : MarkedSSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x y : X.underlying.obj n) :
    (MarkedPresheaf.forget.map ((cartesianCylinder.{u}.endpoint false).app X)).app n x ≠
      (MarkedPresheaf.forget.map ((cartesianCylinder.{u}.endpoint true).app X)).app n y := by
  intro h
  let G : MarkedSSet.{u} ⥤ Type u := MarkedPresheaf.forget ⋙ (evaluation _ _).obj n
  have hc := (Types.binaryCofan_isColimit_iff _).1
    ⟨isColimitOfHasBinaryCoproductOfPreservesColimit G X X⟩
  have hm : Function.Injective (G.map (cartesianCylinder.{u}.endpoints X)) :=
    (mono_iff_injective _).1 (G.map_mono _)
  have h₀ : G.map (cartesianCylinder.{u}.endpoints X) (G.map coprod.inl x) =
      G.map ((cartesianCylinder.{u}.endpoint false).app X) x := by
    rw [← cartesianCylinder.{u}.inl_endpoints, G.map_comp]
    rfl
  have h₁ : G.map (cartesianCylinder.{u}.endpoints X) (G.map coprod.inr y) =
      G.map ((cartesianCylinder.{u}.endpoint true).app X) y := by
    rw [← cartesianCylinder.{u}.inr_endpoints, G.map_comp]
    rfl
  have h' := h₀.trans (h.trans h₁.symm)
  exact Set.disjoint_left.1 hc.2.2.disjoint ⟨x, rfl⟩ ⟨y, (hm h').symm⟩

section MappingCylinder

variable {Φ Ψ : SSet.{u} ⥤ MarkedSSet.{u}} (α : Φ ⟶ Ψ)

private noncomputable def cylinderSpan : SSet.{u} ⥤ WalkingSpan ⥤ MarkedSSet.{u} where
  obj X := span ((cartesianCylinder.{u}.endpoint true).app (Φ.obj X)) (α.app X)
  map f := spanHomMk (Φ.map f) (cartesianCylinder.{u}.I.map (Φ.map f)) (Ψ.map f)
    (cartesianCylinder.{u}.endpoint_naturality true (Φ.map f)) (α.naturality f).symm
  map_id _ := by ext (_ | _ | _) <;> dsimp [spanHomMk] <;> simp
  map_comp _ _ := by ext (_ | _ | _) <;> dsimp [spanHomMk] <;> simp

private instance preservesColimitsOfSize_cylinderSpan [PreservesColimitsOfSize.{u, u} Φ]
    [PreservesColimitsOfSize.{u, u} Ψ] : PreservesColimitsOfSize.{u, u} (cylinderSpan α) := by
  refine ⟨fun {K} _ ↦ preservesColimitsOfShape_of_evaluation _ _ fun k ↦ ?_⟩
  rcases k with _ | _ | _
  · exact preservesColimitsOfShape_of_natIso (F := Φ)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦
        (Category.comp_id _).trans (Category.id_comp (Φ.map f)).symm)
  · exact preservesColimitsOfShape_of_natIso (F := Φ ⋙ cartesianCylinder.{u}.I)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦
        (Category.comp_id _).trans (Category.id_comp (cartesianCylinder.{u}.I.map (Φ.map f))).symm)
  · exact preservesColimitsOfShape_of_natIso (F := Ψ)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦
        (Category.comp_id _).trans (Category.id_comp (Ψ.map f)).symm)

private noncomputable abbrev mappingCylinder : SSet.{u} ⥤ MarkedSSet.{u} where
  obj X := pushout ((cartesianCylinder.{u}.endpoint true).app (Φ.obj X)) (α.app X)
  map f := pushout.desc (cartesianCylinder.{u}.I.map (Φ.map f) ≫ pushout.inl _ _)
    (Ψ.map f ≫ pushout.inr _ _) (by
      rw [← Category.assoc, cartesianCylinder.{u}.endpoint_naturality, Category.assoc,
        pushout.condition, ← α.naturality_assoc])
  map_id X := pushout.hom_ext (by simp) (by simp)
  map_comp f g := pushout.hom_ext
    (by rw [pushout.inl_desc, pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc,
      Functor.map_comp, Functor.map_comp, Category.assoc])
    (by rw [pushout.inr_desc, pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc,
      Functor.map_comp, Category.assoc])

@[reassoc (attr := simp)]
private theorem inl_mappingCylinder_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inl _ _ ≫ (mappingCylinder α).map f =
      cartesianCylinder.{u}.I.map (Φ.map f) ≫ pushout.inl _ _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
private theorem inr_mappingCylinder_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inr _ _ ≫ (mappingCylinder α).map f = Ψ.map f ≫ pushout.inr _ _ :=
  pushout.inr_desc _ _ _

private noncomputable def cylinderSpanCompColimIso : cylinderSpan α ⋙ colim ≅ mappingCylinder α :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    refine (Category.comp_id _).trans ((Category.id_comp _).symm.trans ?_).symm
    refine pushout.hom_ext ?_ ?_
    · exact (congrArg (pushout.inl _ _ ≫ ·) ((Category.id_comp _).trans (Category.id_comp _))).trans
        ((inl_mappingCylinder_map α f).trans
          (colimit.ι_map ((cylinderSpan α).map f) WalkingSpan.left).symm)
    · exact (congrArg (pushout.inr _ _ ≫ ·) ((Category.id_comp _).trans (Category.id_comp _))).trans
        ((inr_mappingCylinder_map α f).trans
          (colimit.ι_map ((cylinderSpan α).map f) WalkingSpan.right).symm)

private instance preservesColimitsOfSize_mappingCylinder [PreservesColimitsOfSize.{u, u} Φ]
    [PreservesColimitsOfSize.{u, u} Ψ] : PreservesColimitsOfSize.{u, u} (mappingCylinder α) :=
  ⟨fun {_} _ ↦ preservesColimitsOfShape_of_natIso (cylinderSpanCompColimIso α)⟩

private noncomputable def mappingCylinderIncl : Φ ⟶ mappingCylinder α where
  app X := (cartesianCylinder.{u}.endpoint false).app (Φ.obj X) ≫ pushout.inl _ _
  naturality X Y f := by
    rw [Category.assoc, inl_mappingCylinder_map, cartesianCylinder.{u}.endpoint_naturality_assoc]

private noncomputable def mappingCylinderProj : mappingCylinder α ⟶ Ψ where
  app X := pushout.desc (cartesianCylinder.{u}.contraction.app (Φ.obj X) ≫ α.app X) (𝟙 _) (by
    rw [cartesianCylinder.{u}.endpoint_app_contraction_app_assoc, Category.comp_id])
  naturality X Y f := by
    refine pushout.hom_ext ?_ ?_
    · rw [inl_mappingCylinder_map_assoc, pushout.inl_desc, pushout.inl_desc_assoc,
        cartesianCylinder.{u}.map_contraction_app_assoc, α.naturality, Category.assoc]
    · rw [inr_mappingCylinder_map_assoc, pushout.inr_desc, pushout.inr_desc_assoc,
        Category.comp_id, Category.id_comp]

@[reassoc]
private theorem mappingCylinderIncl_app_comp_proj_app (X : SSet.{u}) :
    (mappingCylinderIncl α).app X ≫ (mappingCylinderProj α).app X = α.app X := by
  change (_ ≫ pushout.inl _ _) ≫ pushout.desc _ _ _ = _
  rw [Category.assoc, pushout.inl_desc, cartesianCylinder.{u}.endpoint_app_contraction_app_assoc]

private noncomputable def cylinderBox {A B : SSet.{u}} (i : A ⟶ B) :
    pushout ((mappingCylinderIncl α).app A) (Φ.map i) ⟶ (mappingCylinder α).obj B :=
  pushout.desc ((mappingCylinder α).map i) ((mappingCylinderIncl α).app B)
    ((mappingCylinderIncl α).naturality i).symm

private theorem mono_cylinderBox [Φ.PreservesMonomorphisms] [Ψ.PreservesMonomorphisms]
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] : Mono (cylinderBox α i) := by
  let e₀ := cartesianCylinder.{u}.endpoint false
  let e₁ := cartesianCylinder.{u}.endpoint true
  have hBox := IsPushout.of_hasPushout (e₀.app (Φ.obj A)) (Φ.map i)
  have hMA := IsPushout.of_hasPushout (e₁.app (Φ.obj A)) (α.app A)
  have hMB := IsPushout.of_hasPushout (e₁.app (Φ.obj B)) (α.app B)
  have hS := IsPushout.of_hasPushout ((mappingCylinderIncl α).app A) (Φ.map i)
  have hw : pushout.inl (e₁.app (Φ.obj A)) (α.app A) ≫ pushout.inl _ (Φ.map i) =
      pushout.inl _ _ ≫ hBox.desc (pushout.inl (e₁.app (Φ.obj A)) (α.app A) ≫
        pushout.inl ((mappingCylinderIncl α).app A) (Φ.map i))
        (pushout.inr ((mappingCylinderIncl α).app A) (Φ.map i))
        ((Category.assoc _ _ _).symm.trans hS.w) :=
    (hBox.inl_desc _ _ _).symm
  have hQ := (hBox.paste_horiz_iff hw).1 (by rw [hBox.inr_desc]; exact hS)
  have hP := hMA.flip.paste_vert hQ
  have hpb := isPullback_comp_of_isPushout (hBox.map MarkedPresheaf.forget)
    ((MarkedPresheaf.forget.map_comp _ _).symm.trans
      (congrArg MarkedPresheaf.forget.map (cartesianCylinder.{u}.inl_endpointBox false _)))
    ((MarkedPresheaf.forget.map_comp _ _).symm.trans
      (congrArg MarkedPresheaf.forget.map (cartesianCylinder.{u}.inr_endpointBox false _)))
    ((cartesianCylinder.{u}.isPullback_endpoint true (Φ.map i)).map MarkedPresheaf.forget)
    (forget_map_endpoint_app_ne (Φ.obj B))
  rw [← MarkedPresheaf.forget.map_comp] at hpb
  rw [MarkedPresheaf.mono_iff]
  refine mono_of_isPushout_of_isPullback (hP.flip.map MarkedPresheaf.forget)
    (hMB.map MarkedPresheaf.forget) hpb
    (hf' := (MarkedPresheaf.mono_iff _).1 (cartesianCylinder.{u}.mono_endpoint true (Φ.obj B)))
    (hu₁ := (MarkedPresheaf.mono_iff _).1
      (cartesianCylinder.{u}.mono_endpointBox false (Φ.map i) inferInstance))
    (hu₂ := (MarkedPresheaf.mono_iff _).1 inferInstance)
    (by rw [← MarkedPresheaf.forget.map_comp, ← MarkedPresheaf.forget.map_comp, α.naturality]) ?_ ?_
  · refine (Functor.map_comp _ _ _).symm.trans (Eq.trans (congrArg _ (hBox.hom_ext ?_ ?_))
      (Functor.map_comp _ _ _))
    · rw [hBox.inl_desc_assoc, Category.assoc, cylinderBox, pushout.inl_desc,
        inl_mappingCylinder_map, cartesianCylinder.{u}.inl_endpointBox_assoc]
    · rw [hBox.inr_desc_assoc, cylinderBox, pushout.inr_desc,
        cartesianCylinder.{u}.inr_endpointBox_assoc]
      rfl
  · refine (Functor.map_comp _ _ _).symm.trans (Eq.trans (congrArg _ ?_)
      (Functor.map_comp _ _ _))
    rw [Category.assoc, cylinderBox, pushout.inl_desc, inr_mappingCylinder_map]

private theorem trivialCofibrations_inr_mappingCylinder (X : SSet.{u}) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (pushout.inr ((cartesianCylinder.{u}.endpoint true).app (Φ.obj X)) (α.app X)) := by
  have := cartesianCylinder.{u}.isSaturated_trivialCofibrations cartesianGenerators
    cartesianGenerators_le_monomorphisms
  have h := cartesianCylinder.{u}.anodyne_endpoint_app (S := cartesianGenerators) true (Φ.obj X)
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout _ _).flip
    ⟨cartesianCylinder.{u}.anodyne_le_monomorphisms _ cartesianGenerators_le_monomorphisms _ h,
      cartesianCylinder.{u}.anodyne_le_weakEquivalences _ cartesianGenerators_le_monomorphisms _ h⟩

private theorem weakEquivalences_mappingCylinderProj_app (X : SSet.{u}) :
    weakEquivalences MarkedSSet.{u} ((mappingCylinderProj α).app X) :=
  (weakEquivalences MarkedSSet.{u}).of_precomp (W' := weakEquivalences MarkedSSet.{u}) _ _
    (trivialCofibrations_inr_mappingCylinder α X).2
    (by rw [mappingCylinderProj, pushout.inr_desc]; exact (weakEquivalences _).id_mem _)

private theorem weakEquivalences_mappingCylinderIncl_app_iff (X : SSet.{u}) :
    weakEquivalences MarkedSSet.{u} ((mappingCylinderIncl α).app X) ↔
      weakEquivalences MarkedSSet.{u} (α.app X) := by
  refine ⟨fun h ↦ ?_, fun h ↦ (weakEquivalences _).of_postcomp _ _
    (weakEquivalences_mappingCylinderProj_app α X)
    ((mappingCylinderIncl_app_comp_proj_app α X).symm ▸ h)⟩
  rw [← mappingCylinderIncl_app_comp_proj_app α X]
  exact (weakEquivalences _).comp_mem _ _ h (weakEquivalences_mappingCylinderProj_app α X)

private theorem trivialCofibrations_cylinderBox [Φ.PreservesMonomorphisms]
    [Ψ.PreservesMonomorphisms] {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hA : weakEquivalences MarkedSSet.{u} (α.app A))
    (hB : weakEquivalences MarkedSSet.{u} (α.app B)) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators (cylinderBox α i) := by
  refine ⟨mono_cylinderBox α i, ?_⟩
  have hS := IsPushout.of_hasPushout ((mappingCylinderIncl α).app A) (Φ.map i)
  have h₂ :
      weakEquivalences MarkedSSet.{u} (pushout.inr ((mappingCylinderIncl α).app A) (Φ.map i)) :=
    cartesianCylinder.{u}.weakEquivalences_of_isPushout cartesianGenerators_le_monomorphisms hS.flip
      ((weakEquivalences_mappingCylinderIncl_app_iff α A).2 hA)
  refine (weakEquivalences MarkedSSet.{u}).of_precomp _ _ h₂ ?_
  rw [cylinderBox, pushout.inr_desc]
  exact (weakEquivalences_mappingCylinderIncl_app_iff α B).2 hB

end MappingCylinder

section Induction

variable (Φ Ψ : SSet.{u} ⥤ MarkedSSet.{u}) [PreservesColimitsOfSize.{u, u} Φ]
  [PreservesColimitsOfSize.{u, u} Ψ] [Φ.PreservesMonomorphisms] [Ψ.PreservesMonomorphisms]
  (α : Φ ⟶ Ψ)

private theorem weakEquivalences_app_boundary
    (h : ∀ n : ℕ, weakEquivalences MarkedSSet.{u} (α.app Δ[n])) (n : ℕ) :
    weakEquivalences MarkedSSet.{u} (α.app ∂Δ[n]) := by
  refine prop_boundary (fun X ↦ weakEquivalences MarkedSSet.{u} (α.app X)) (fun e hX ↦ ?_)
    (fun sq hf h₀ h₁ h₂ ↦ ?_) ?_ h n
  · exact ((weakEquivalences MarkedSSet.{u}).arrow_mk_iso_iff
      (Arrow.isoMk (Φ.mapIso e) (Ψ.mapIso e) (α.naturality e.hom))).1 hX
  · have := hf
    exact cartesianCylinder.{u}.weakEquivalences_of_isPushout_of_mono
      cartesianGenerators_le_monomorphisms (sq.map Φ) (sq.map Ψ) (α.app _) (α.app _) (α.app _)
      (α.app _) (α.naturality _) (α.naturality _) (α.naturality _) (α.naturality _) h₀ h₁ h₂
  · have hΦ : IsInitial (Φ.obj (⊥_ SSet.{u})) := IsInitial.isInitialObj Φ _ initialIsInitial
    have hΨ : IsInitial (Ψ.obj (⊥_ SSet.{u})) := IsInitial.isInitialObj Ψ _ initialIsInitial
    have : IsIso (α.app (⊥_ SSet.{u})) := ⟨⟨hΨ.to _, hΦ.hom_ext _ _, hΨ.hom_ext _ _⟩⟩
    exact (weakEquivalences MarkedSSet.{u}).of_isIso _

theorem MarkedSSet.weakEquivalence_app_of_stdSimplex
    (h : ∀ n : ℕ, WeakEquivalence (α.app Δ[n])) (X : SSet.{u}) :
    WeakEquivalence (α.app X) := by
  replace h : ∀ n : ℕ, weakEquivalences MarkedSSet.{u} (α.app Δ[n]) := fun n ↦
    (weakEquivalence_iff _).1 (h n)
  rw [weakEquivalence_iff]
  let ι := Functor.whiskerLeft (MarkedPresheaf.forget (D := edgeMarking)) (mappingCylinderIncl α)
  have := cartesianCylinder.{u}.isSaturated_trivialCofibrations cartesianGenerators
    cartesianGenerators_le_monomorphisms
  have := NatTrans.isSaturated_leibnizPreimage ι
    (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators)
  have : PreservesColimitsOfSize.{u, u} (MarkedPresheaf.flat edgeMarking) :=
    (MarkedPresheaf.flatForgetAdjunction edgeMarking).leftAdjoint_preservesColimits
  have hle : monomorphisms SSet.{u} ≤ (NatTrans.leibnizPreimage ι
      (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators)).inverseImage
      (MarkedPresheaf.flat edgeMarking) := by
    rw [← saturation_I_eq_monomorphisms]
    refine saturation_le _ _ ?_
    rintro _ _ _ ⟨n⟩
    exact trivialCofibrations_cylinderBox α _ (weakEquivalences_app_boundary Φ Ψ α h n) (h n)
  have hX : cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (cylinderBox α (initial.to X)) := hle _ (monomorphisms.infer_property _)
  have hS := IsPushout.of_hasPushout ((mappingCylinderIncl α).app (⊥_ SSet.{u}))
    (Φ.map (initial.to X))
  have hΦ : IsInitial (Φ.obj (⊥_ SSet.{u})) := IsInitial.isInitialObj Φ _ initialIsInitial
  have hM : IsInitial ((mappingCylinder α).obj (⊥_ SSet.{u})) :=
    IsInitial.isInitialObj _ _ initialIsInitial
  have : IsIso ((mappingCylinderIncl α).app (⊥_ SSet.{u})) :=
    ⟨⟨hM.to _, hΦ.hom_ext _ _, hM.hom_ext _ _⟩⟩
  have := hS.isIso_inr_of_isIso
  refine (weakEquivalences_mappingCylinderIncl_app_iff α X).1 ?_
  rw [← pushout.inr_desc ((mappingCylinder α).map (initial.to X))
    ((mappingCylinderIncl α).app X) ((mappingCylinderIncl α).naturality (initial.to X)).symm]
  exact (weakEquivalences MarkedSSet.{u}).comp_mem _ _
    ((weakEquivalences MarkedSSet.{u}).of_isIso _) hX.2

end Induction

section OverMarking

variable (X : SSet.{u}) (M : Set (X _⦋1⦌))

noncomputable def overMarking : Over X ⥤ MarkedSSet.{u} where
  obj T := MarkedSSet.ofEdgeSet T.left {e | T.hom.app _ e ∈ M}
  map {T T'} g := MarkedSSet.ofEdgeSetHom g.left _ _ fun e he => by
    have h := congr_app (Over.w g) (Opposite.op ⦋1⦌)
    rw [NatTrans.comp_app] at h
    rw [Set.mem_ofPred_eq, ← types_comp_apply (g.left.app _) (T'.hom.app _), h]
    exact he
  map_id _ := MarkedPresheaf.hom_ext rfl
  map_comp _ _ := MarkedPresheaf.hom_ext rfl

variable {X M}

noncomputable def isColimitOverMarkingMapCocone {K : Type w} [SmallCategory K] [UnivLE.{w, u}]
    {G : K ⥤ Over X}
    {c : Cocone G} (hc : IsColimit ((Over.forget X).mapCocone c)) :
    IsColimit ((overMarking X M).mapCocone c) :=
  MarkedPresheaf.isColimitOfForget _ hc fun ⟨n⟩ y hy => by
    obtain rfl : n = 1 := MarkedSSet.len_eq_one_of_mem_marked _ hy
    have hs (m : SimplexCategoryᵒᵖ) (z : c.pt.left.obj m) :
        ∃ j, ∃ x : (G.obj j).left.obj m, (c.ι.app j).left.app m x = z :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves ((evaluation _ _).obj m) hc) z
    rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ y).1 hy with hy | ⟨v, rfl⟩
    · obtain ⟨j, x, rfl⟩ := hs _ y
      refine ⟨j, x, (MarkedSSet.mem_marked_ofEdgeSet _ _ x).2 (Or.inl ?_), rfl⟩
      have h := congr_app (Over.w (c.ι.app j)) (Opposite.op ⦋1⦌)
      rw [NatTrans.comp_app] at h
      rw [Set.mem_ofPred_eq, ← h]
      exact hy
    · obtain ⟨j, x, rfl⟩ := hs _ v
      exact ⟨j, (G.obj j).left.σ 0 x, (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inr ⟨x, rfl⟩),
        SSet.σ_naturality_apply (c.ι.app j).left 0 x⟩

theorem isPushout_overMarking_map {P₀ P₁ P₂ P₃ : Over X} {f₁ : P₀ ⟶ P₁} {f₂ : P₀ ⟶ P₂}
    {g₁ : P₁ ⟶ P₃} {g₂ : P₂ ⟶ P₃} (h : IsPushout f₁.left f₂.left g₁.left g₂.left) :
    IsPushout ((overMarking X M).map f₁) ((overMarking X M).map f₂)
      ((overMarking X M).map g₁) ((overMarking X M).map g₂) := by
  have w : f₁ ≫ g₁ = f₂ ≫ g₂ := Over.OverMorphism.ext h.w
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ ((Functor.map_comp _ _ _).symm.trans
    ((congrArg _ w).trans (Functor.map_comp _ _ _)))) ?_
  refine (isColimitMapCoconePushoutCoconeEquiv (overMarking X M) w)
    (isColimitOverMarkingMapCocone (M := M)
      ((isColimitMapCoconePushoutCoconeEquiv (Over.forget X) w).symm h.isColimit))

section RelativeCellComplex

variable {J : Type} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type u} {A B : (j : J) → α j → SSet.{u}}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} {Y : SSet.{u}} {f : Y ⟶ X}

theorem trivialCofibrations_overMarking_map_of_relativeCellComplex
    (c : RelativeCellComplex.{u} basicCell f)
    (hcell : ∀ (j : J) (hj : ¬ IsMax j) (i : (c.attachCells j hj).ι),
      cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
        ((overMarking X M).map (Over.homMk (basicCell j ((c.attachCells j hj).π i)) rfl :
          Over.mk (basicCell j _ ≫ (c.attachCells j hj).cell i ≫ c.incl.app (Order.succ j)) ⟶
            Over.mk ((c.attachCells j hj).cell i ≫ c.incl.app (Order.succ j))))) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators ((overMarking X M).map
      (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 X))) := by
  have := cartesianCylinder.{u}.isSaturated_trivialCofibrations cartesianGenerators
    cartesianGenerators_le_monomorphisms
  let G := c.F.toOver X c.incl.app fun g ↦ (c.incl.naturality g).trans (Category.comp_id _)
  let cO : Cocone G :=
    { pt := Over.mk (𝟙 X)
      ι := { app j := Over.homMk (c.incl.app j)
             naturality _ _ g := Over.OverMorphism.ext (c.incl.naturality g) } }
  have hcO : IsColimit ((Over.forget X).mapCocone cO) := c.isColimit
  have := IsCellularlyClosed.isStableUnderCoproducts.{u}
    (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators)
  have hle :
      (coproducts.{u} (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators)).pushouts ≤
        cartesianCylinder.{u}.trivialCofibrations cartesianGenerators := by
    rw [pushouts_le_iff, coproducts_le_iff]
  let T :
      (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).TransfiniteCompositionOfShape
        J ((overMarking X M).map (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 X))) :=
    { F := G ⋙ overMarking X M
      isoBot := (overMarking X M).mapIso (Over.isoMk c.isoBot
        ((congrArg (c.isoBot.hom ≫ ·) c.fac.symm).trans (c.isoBot.hom_inv_id_assoc _)))
      isWellOrderContinuous := ⟨fun m hm ↦
        ⟨isColimitOverMarkingMapCocone (M := M) (c := (Set.principalSegIio m).cocone G)
          (c.F.isColimitOfIsWellOrderContinuous m hm)⟩⟩
      incl := ((overMarking X M).mapCocone cO).ι
      isColimit := isColimitOverMarkingMapCocone (M := M) hcO
      fac := MarkedPresheaf.hom_ext c.fac
      map_mem j hj := hle _ (by
        let a := c.attachCells j hj
        have hw : a.m ≫ a.g₂ ≫ c.incl.app (Order.succ j) = a.g₁ ≫ c.incl.app j := by
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c.incl.app (Order.succ j))
            a.isPushout.w.symm).trans (Category.assoc _ _ _)) |>.trans
            (congrArg (a.g₁ ≫ ·) ((c.incl.naturality _).trans (Category.comp_id _)))
        let Q₁ : Over X := Over.mk (a.g₁ ≫ c.incl.app j)
        let Q₂ : Over X := Over.mk (a.g₂ ≫ c.incl.app (Order.succ j))
        let mO : Q₁ ⟶ Q₂ := Over.homMk a.m hw
        have hsq := isPushout_overMarking_map (M := M) (f₁ := (Over.homMk a.g₁ : Q₁ ⟶ G.obj j))
          (f₂ := mO) (g₁ := G.map (homOfLE (Order.le_succ j)))
          (g₂ := (Over.homMk a.g₂ : Q₂ ⟶ G.obj (Order.succ j))) a.isPushout
        refine ⟨_, _, _, _, _, ?_, hsq⟩
        let Aover : a.ι → Over X := fun i ↦
          Over.mk (basicCell j (a.π i) ≫ a.cell i ≫ c.incl.app (Order.succ j))
        let Bover : a.ι → Over X := fun i ↦ Over.mk (a.cell i ≫ c.incl.app (Order.succ j))
        have h₁ (i : a.ι) : a.cofan₁.inj i ≫ Q₁.hom = (Aover i).hom :=
          (congrArg (a.cofan₁.inj i ≫ ·) hw.symm).trans
            ((reassoc_of% (a.hm i)) _)
        let c₁ : Cofan Aover := Cofan.mk Q₁ fun i ↦ Over.homMk (a.cofan₁.inj i) (h₁ i)
        let c₂ : Cofan Bover :=
          Cofan.mk Q₂ fun i ↦ Over.homMk (a.cofan₂.inj i) (Category.assoc _ _ _).symm
        have hc₁ : IsColimit ((Over.forget X).mapCocone c₁) :=
          (isColimitMapCoconeCofanMkEquiv (Over.forget X) _ _).symm
            (a.isColimit₁.ofIsoColimit (Cofan.ext (Iso.refl _) fun i ↦ Category.comp_id _))
        have hc₂ : IsColimit ((Over.forget X).mapCocone c₂) :=
          (isColimitMapCoconeCofanMkEquiv (Over.forget X) _ _).symm
            (a.isColimit₂.ofIsoColimit (Cofan.ext (Iso.refl _) fun i ↦ Category.comp_id _))
        refine colimitsOfShape_le_coproducts _ a.ι _ (colimitsOfShape.mk' _ _ _ _
          (isColimitOverMarkingMapCocone (M := M) hc₁) (isColimitOverMarkingMapCocone (M := M) hc₂)
          (Functor.whiskerRight (Discrete.natTrans fun i ↦
            (Over.homMk (basicCell j (a.π i.as)) rfl : Aover i.as ⟶ Bover i.as)) (overMarking X M))
          (fun i ↦ hcell j hj i.as) ((overMarking X M).map mO) fun i ↦ MarkedPresheaf.hom_ext ?_)
        exact a.hm i.as) }
  have := IsStableUnderTransfiniteComposition.shrink₀
    (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators)
  exact transfiniteCompositionsOfShape_le _ J _ ⟨T⟩

end RelativeCellComplex

end OverMarking

section Horn

theorem trivialCofibrations_ofEdgeSetHom_of_subset {K L : SSet.{u}} (j : K ⟶ L)
    {E₀ E₁ : Set (K _⦋1⦌)} {F₀ F₁ : Set (L _⦋1⦌)} (hE : E₀ ⊆ E₁)
    (hF₀ : ∀ e ∈ E₀, j.app _ e ∈ F₀) (hF₁ : ∀ e ∈ E₁, j.app _ e ∈ F₁)
    (hF₀₁ : F₀ ⊆ F₁) (hF : ∀ e ∈ F₁, ∃ e' ∈ E₁, j.app _ e' = e)
    (h : cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (MarkedSSet.ofEdgeSetHom j E₀ F₀ hF₀)) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (MarkedSSet.ofEdgeSetHom j E₁ F₁ hF₁) := by
  have := cartesianCylinder.{u}.isSaturated_trivialCofibrations cartesianGenerators
    cartesianGenerators_le_monomorphisms
  have hsq : IsPushout (MarkedSSet.ofEdgeSetHom j E₀ F₀ hF₀)
      (MarkedSSet.ofEdgeSetHom (𝟙 K) E₀ E₁ fun e he ↦ hE he)
      (MarkedSSet.ofEdgeSetHom (𝟙 L) F₀ F₁ fun e he ↦ hF₀₁ he)
      (MarkedSSet.ofEdgeSetHom j E₁ F₁ hF₁) := by
    refine IsPushout.of_isColimit (c := PushoutCocone.mk (f := MarkedSSet.ofEdgeSetHom j E₀ F₀ hF₀)
      (g := MarkedSSet.ofEdgeSetHom (𝟙 K) E₀ E₁ fun e he ↦ hE he)
      (MarkedSSet.ofEdgeSetHom (𝟙 L) F₀ F₁ fun e he ↦ hF₀₁ he)
      (MarkedSSet.ofEdgeSetHom j E₁ F₁ hF₁) (MarkedPresheaf.hom_ext (IsPushout.id_vert j).w))
      (MarkedPresheaf.isColimitOfForget _ ?_ fun ⟨n⟩ y hy ↦ ?_)
    · exact (isColimitMapCoconePushoutCoconeEquiv MarkedPresheaf.forget _).symm
        (IsPushout.id_vert j).isColimit
    · obtain rfl : n = 1 := MarkedSSet.len_eq_one_of_mem_marked _ hy
      rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ y).1 hy with hy | ⟨v, rfl⟩
      · obtain ⟨e', he', rfl⟩ := hF y hy
        exact ⟨WalkingSpan.right, e', (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl he'), rfl⟩
      · exact ⟨WalkingSpan.left, L.σ 0 v,
          (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inr ⟨v, rfl⟩), rfl⟩
  exact MorphismProperty.of_isPushout hsq.flip h

theorem trivialCofibrations_ofEdgeSetHom_horn_ι {n : ℕ} (i : Fin (n + 3)) (h0 : 0 < i)
    (hn : i < Fin.last (n + 2)) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (MarkedSSet.ofEdgeSetHom Λ[n + 2, i].ι ∅ ∅ fun _ h ↦ h.elim) := by
  have := cartesianCylinder.{u}.isSaturated_trivialCofibrations cartesianGenerators
    cartesianGenerators_le_monomorphisms
  have h := cartesianCylinder.{u}.le_anodyne cartesianGenerators _
    (cartesianGenerators.innerHorn i h0 hn)
  have hT : cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      ((MarkedPresheaf.flat edgeMarking).map Λ[n + 2, i].ι) :=
    ⟨cartesianCylinder.{u}.anodyne_le_monomorphisms _ cartesianGenerators_le_monomorphisms _ h,
      cartesianCylinder.{u}.anodyne_le_weakEquivalences _ cartesianGenerators_le_monomorphisms _ h⟩
  let e (Z : SSet.{u}) : (MarkedPresheaf.flat edgeMarking).obj Z ≅ MarkedSSet.ofEdgeSet Z ∅ :=
    { hom := edgeHomMk (𝟙 Z) fun x hx ↦ by
        obtain ⟨y, rfl⟩ := exists_eq_σ_of_mem_marked_flat x hx
        exact (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inr ⟨y, rfl⟩)
      inv := edgeHomMk (𝟙 Z) fun x hx ↦ by
        rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ _).1 hx with h | ⟨y, rfl⟩
        · exact h.elim
        · exact MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj Z) y
      hom_inv_id := MarkedPresheaf.hom_ext rfl
      inv_hom_id := MarkedPresheaf.hom_ext rfl }
  exact ((cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).arrow_mk_iso_iff
    (Arrow.isoMk (e _) (e _) (MarkedPresheaf.hom_ext rfl))).1 hT

theorem trivialCofibrations_overMarking_map_horn {X : SSet.{u}} {M : Set (X _⦋1⦌)} {m : ℕ}
    (hm : 1 ≤ m) (i : Fin (m + 2)) (t : Δ[m + 1] ⟶ X)
    (hS : ∀ e : Δ[m + 1] _⦋1⦌, t.app _ e ∈ M → e ∈ (Λ[m + 1, i] : SSet.Subcomplex _).obj _)
    (h₀ : i = 0 → t.app _ (SSet.stdSimplex.edge (m + 1) 0 1 (Fin.zero_le _)) ∈ M)
    (hl : i = Fin.last _ → t.app _ (SSet.stdSimplex.edge (m + 1) (Fin.last m).castSucc
      (Fin.last (m + 1)) (Fin.le_last _)) ∈ M) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators ((overMarking X M).map
      (Over.homMk Λ[m + 1, i].ι rfl : Over.mk (Λ[m + 1, i].ι ≫ t) ⟶ Over.mk t)) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  have hF (e : Δ[d + 2] _⦋1⦌) (he : t.app _ e ∈ M) :
      ∃ e' ∈ {e' | (Λ[d + 2, i].ι ≫ t).app _ e' ∈ M}, Λ[d + 2, i].ι.app _ e' = e :=
    ⟨⟨e, hS e he⟩, he, rfl⟩
  by_cases hi0 : i = 0
  · subst hi0
    have hw := weakEquivalence_ofEdgeSetHom_horn_zero d
    rw [weakEquivalence_iff] at hw
    exact trivialCofibrations_ofEdgeSetHom_of_subset Λ[d + 2, 0].ι
      (E₀ := {SSet.horn.edge (d + 2) 0 0 1 (Fin.zero_le _) (by simp)})
      (F₀ := {Λ[d + 2, 0].ι.app _ (SSet.horn.edge (d + 2) 0 0 1 (Fin.zero_le _) (by simp))})
      (E₁ := {e' | (Λ[d + 2, 0].ι ≫ t).app _ e' ∈ M}) (F₁ := {e | t.app _ e ∈ M})
      (Set.singleton_subset_iff.2 (h₀ rfl)) (fun _ h ↦ by rw [Set.mem_singleton_iff.1 h]; rfl)
      (fun _ h ↦ h) (Set.singleton_subset_iff.2 (h₀ rfl)) hF
      ⟨(MarkedPresheaf.mono_iff _).2 (inferInstance : Mono Λ[d + 2, 0].ι), hw⟩
  by_cases hil : i = Fin.last _
  · subst hil
    have hw := weakEquivalence_ofEdgeSetHom_horn_last d
    rw [weakEquivalence_iff] at hw
    exact trivialCofibrations_ofEdgeSetHom_of_subset Λ[d + 2, Fin.last (d + 2)].ι
      (E₀ := {SSet.horn.edge (d + 2) (Fin.last (d + 2)) (Fin.last (d + 1)).castSucc
        (Fin.last (d + 2)) (Fin.le_last _) (by simp)})
      (F₀ := {Λ[d + 2, Fin.last (d + 2)].ι.app _ (SSet.horn.edge (d + 2) (Fin.last (d + 2))
        (Fin.last (d + 1)).castSucc (Fin.last (d + 2)) (Fin.le_last _) (by simp))})
      (E₁ := {e' | (Λ[d + 2, Fin.last (d + 2)].ι ≫ t).app _ e' ∈ M}) (F₁ := {e | t.app _ e ∈ M})
      (Set.singleton_subset_iff.2 (hl rfl)) (fun _ h ↦ by rw [Set.mem_singleton_iff.1 h]; rfl)
      (fun _ h ↦ h) (Set.singleton_subset_iff.2 (hl rfl)) hF
      ⟨(MarkedPresheaf.mono_iff _).2 (inferInstance : Mono Λ[d + 2, Fin.last (d + 2)].ι), hw⟩
  exact trivialCofibrations_ofEdgeSetHom_of_subset Λ[d + 2, i].ι (E₀ := ∅) (F₀ := ∅)
    (E₁ := {e' | (Λ[d + 2, i].ι ≫ t).app _ e' ∈ M}) (F₁ := {e | t.app _ e ∈ M})
    (Set.empty_subset _) (fun _ h ↦ h.elim) (fun _ h ↦ h) (Set.empty_subset _) hF
    (trivialCofibrations_ofEdgeSetHom_horn_ι i (Fin.pos_iff_ne_zero.2 hi0)
      (Fin.lt_last_iff_ne_last.2 hil))

end Horn

section Prism

open SSet MonoidalCategory

variable (n : ℕ)

def verticalEdges : Set ((Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋1⦌) := {e | e.2 0 = e.2 1}

variable {n}

theorem surjective_snd_of_notMem_unionProd {k : ℕ} (z : (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋k⦌)
    (hz : z ∉ (Subcomplex.unionProd Λ[1, 0] ∂Δ[n]).obj _) : Function.Surjective z.2 := by
  intro b
  by_contra h
  exact hz ((Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl ((mem_boundary_iff_notMem_range _).2
    ⟨b, fun ⟨a, ha⟩ ↦ h ⟨a, ha⟩⟩)))

theorem app_objEquiv_symm_snd_apply {k l : ℕ} (t : Δ[k] ⟶ (Δ[1] ⊗ Δ[n] : SSet.{u}))
    (g : ⦋l⦌ ⟶ ⦋k⦌) (a : Fin (l + 1)) :
    (t.app _ (stdSimplex.objEquiv.symm g)).2 a = (yonedaEquiv t).2 (g.toOrderHom a) := by
  rw [← Equiv.symm_apply_apply yonedaEquiv t]
  rfl

theorem trivialCofibrations_overMarking_map_unionProd_ι (hn : 1 ≤ n) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      ((overMarking _ (verticalEdges n)).map
        (Over.homMk (Subcomplex.unionProd Λ[1, 0] ∂Δ[n]).ι :
          Over.mk (Subcomplex.unionProd Λ[1, 0] ∂Δ[n]).ι ⟶ Over.mk (𝟙 _))) := by
  let P := prodStdSimplex.pairing.{u} (0 : Fin 2) n
  refine trivialCofibrations_overMarking_map_of_relativeCellComplex
    P.rankFunction.relativeCellComplex fun j hj c ↦ ?_
  let c' : P.rankFunction.Cell j := c
  have ht : (P.rankFunction.relativeCellComplex.attachCells j hj).cell c ≫
      P.rankFunction.relativeCellComplex.incl.app (Order.succ j) = c'.map :=
    (Category.assoc _ _ _).trans ((c'.ι_b_assoc _).trans c'.mapToSucc_ι)
  have hII : c'.map.app _ (stdSimplex.objEquiv.symm (SimplexCategory.δ c'.index)) ∉
      (Subcomplex.unionProd Λ[1, 0] ∂Δ[n]).obj _ := by
    rw [c'.map_app_objEquiv_symm_δ_index]
    exact c'.s.val.notMem
  set x := (yonedaEquiv c'.map).2 with hx
  have hsurj (b : Fin (n + 1)) : ∃ a, x (c'.index.succAbove a) = b := by
    obtain ⟨a, ha⟩ := surjective_snd_of_notMem_unionProd _ hII b
    exact ⟨a, (app_objEquiv_symm_snd_apply _ _ a).symm.trans ha⟩
  have hmono := stdSimplex.monotone_apply (yonedaEquiv c'.map).2
  have happ (e : Δ[c'.dim + 1] _⦋1⦌) (a : Fin 2) : (c'.map.app _ e).2 a = x (e a) := by
    rw [← Equiv.symm_apply_apply stdSimplex.objEquiv e]
    exact app_objEquiv_symm_snd_apply _ _ a
  refine trivialCofibrations_overMarking_map_horn (m := c'.dim) ?_ c'.index _ ?_ ?_ ?_
  · have := Fintype.card_le_of_surjective _ fun b ↦ hsurj b
    simp only [Fintype.card_fin] at this
    omega
  · intro e he
    rw [ht] at he
    change (c'.map.app _ e).2 0 = (c'.map.app _ e).2 1 at he
    rw [happ, happ] at he
    rw [mem_horn_iff_notMem_range]
    by_contra hcon
    push Not at hcon
    have hc (a : Fin (c'.dim + 1)) : x (c'.index.succAbove a) = x (e 0) := by
      obtain ⟨k, hk⟩ := hcon _ (Fin.succAbove_ne _ a)
      rw [← hk]
      fin_cases k
      · rfl
      · exact he.symm
    obtain ⟨a₀, ha₀⟩ := hsurj 0
    obtain ⟨a₁, ha₁⟩ := hsurj 1
    have h01 : (0 : Fin (n + 1)) = 1 := by rw [← ha₀, ← ha₁, hc, hc]
    exact absurd (congrArg Fin.val h01) (by simp; omega)
  · intro h0
    rw [ht]
    refine (happ _ 0).trans (Eq.trans ?_ (happ _ 1).symm)
    obtain ⟨a, ha⟩ := hsurj (x 0)
    rw [h0, Fin.succAbove_zero] at ha
    exact le_antisymm (hmono (Fin.zero_le _)) (ha ▸ hmono (Fin.succ_pos a))
  · intro hl
    rw [ht]
    refine (happ _ 0).trans (Eq.trans ?_ (happ _ 1).symm)
    obtain ⟨a, ha⟩ := hsurj (x (Fin.last _))
    rw [hl, Fin.succAbove_last] at ha
    exact le_antisymm (hmono (Fin.le_last _)) (ha ▸ hmono (Fin.castSucc_le_castSucc_iff.2
      (Fin.le_last a)))

end Prism

section SharpEdge

open SSet MonoidalCategory

private abbrev stdEdge : (Δ[1] : SSet.{u}) _⦋1⦌ := stdSimplex.edge 1 0 1 (Fin.zero_le _)

private theorem app_stdEdge {Y : SSet.{u}} (f : Δ[1] ⟶ Y) : f.app _ stdEdge = SSet.yonedaEquiv f :=
  congrArg (f.app _) (stdSimplex.ext _ _ fun a ↦ by fin_cases a <;> rfl)

def sharpEdgeProdObj (X : MarkedSSet.{u}) : MarkedSSet.{u} :=
  MarkedSSet.ofEdges (Δ[1] ⊗ X.underlying) {e | e.2 ∈ X.marked ⦋1⦌}
    fun x ↦ X.map_σ_mem_marked x.2

theorem mem_marked_sharpEdgeProdObj (X : MarkedSSet.{u}) (e : (Δ[1] ⊗ X.underlying : SSet) _⦋1⦌) :
    e ∈ (sharpEdgeProdObj X).marked ⦋1⦌ ↔ e.2 ∈ X.marked ⦋1⦌ :=
  MarkedSSet.mem_marked_ofEdges _ _ _ _

noncomputable def sharpEdgeProd : MarkedSSet.{u} ⥤ MarkedSSet.{u} where
  obj := sharpEdgeProdObj
  map {X Y} f := edgeHomMk (Δ[1] ◁ MarkedPresheaf.forget.map f) fun e he ↦
    (mem_marked_sharpEdgeProdObj Y _).2 (MarkedPresheaf.map_mem_marked f
      ((mem_marked_sharpEdgeProdObj X e).1 he))
  map_id _ := MarkedPresheaf.hom_ext rfl
  map_comp _ _ := MarkedPresheaf.hom_ext rfl

noncomputable def sharpEdgeEndpoint (ε : Fin 2) : 𝟭 MarkedSSet.{u} ⟶ sharpEdgeProd where
  app X := edgeHomMk (Y := sharpEdgeProdObj X)
    (CartesianMonoidalCategory.lift (SSet.const (stdSimplex.obj₀Equiv.symm ε)) (𝟙 _))
    fun _ he ↦ (mem_marked_sharpEdgeProdObj X _).2 he
  naturality _ _ _ := MarkedPresheaf.hom_ext rfl

noncomputable def sharpEdgeProj : sharpEdgeProd ⟶ 𝟭 MarkedSSet.{u} where
  app X := edgeHomMk (X := sharpEdgeProdObj X) (CartesianMonoidalCategory.snd _ _)
    fun e he ↦ (mem_marked_sharpEdgeProdObj X e).1 he
  naturality _ _ _ := MarkedPresheaf.hom_ext rfl

theorem exists_mem_marked_of_isColimit {K : Type u₁} [Category.{v₁} K] {F : K ⥤ MarkedSSet.{u}}
    {c : Cocone F} (hc : IsColimit c) {y : c.pt.underlying _⦋1⦌} (hy : y ∈ c.pt.marked ⦋1⦌) :
    (∃ j, ∃ x ∈ (F.obj j).marked ⦋1⦌, (MarkedPresheaf.forget.map (c.ι.app j)).app _ x = y) ∨
      ∃ v, c.pt.underlying.map (SimplexCategory.σ 0).op v = y := by
  let E : Set (c.pt.underlying _⦋1⦌) :=
    {y | ∃ j, ∃ x ∈ (F.obj j).marked ⦋1⦌, (MarkedPresheaf.forget.map (c.ι.app j)).app _ x = y}
  let c' : Cocone F :=
    { pt := MarkedSSet.ofEdgeSet c.pt.underlying E
      ι := { app j := edgeHomMk (MarkedPresheaf.forget.map (c.ι.app j)) fun x hx ↦
               (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl ⟨j, x, hx, rfl⟩)
             naturality _ _ g := MarkedPresheaf.hom_ext ((Functor.map_comp _ _ _).symm.trans
               ((congrArg MarkedPresheaf.forget.map ((c.ι.naturality g).trans
                 (Category.comp_id _))).trans (Category.comp_id _).symm)) } }
  let incl : c'.pt ⟶ c.pt := edgeHomMk (𝟙 _) fun z hz ↦ by
    rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ _).1 hz with ⟨j, x, hx, rfl⟩ | ⟨v, rfl⟩
    · exact MarkedPresheaf.map_mem_marked (c.ι.app j) hx
    · exact c.pt.map_σ_mem_marked v
  have h : hc.desc c' ≫ incl = 𝟙 _ := hc.hom_ext fun j ↦ by
    rw [hc.fac_assoc, Category.comp_id]
    exact MarkedPresheaf.hom_ext rfl
  have hd : (MarkedPresheaf.forget.map (hc.desc c')).app _ y = y :=
    congrArg (fun φ ↦ (MarkedPresheaf.forget.map φ).app _ y) h
  have := MarkedPresheaf.map_mem_marked (hc.desc c') hy
  rw [hd] at this
  exact (MarkedSSet.mem_marked_ofEdgeSet _ _ _).1 this

instance preservesColimitsOfSize_sharpEdgeProd :
    PreservesColimitsOfSize.{u, u} sharpEdgeProd.{u} :=
  ⟨fun {K} _ ↦ ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨MarkedPresheaf.isColimitOfForget _
    (isColimitOfPreserves (tensorLeft Δ[1]) (isColimitOfPreserves MarkedPresheaf.forget hc))
    fun ⟨n⟩ y hy ↦ by
      obtain rfl : n = 1 := MarkedSSet.len_eq_one_of_mem_marked _ hy
      rcases exists_mem_marked_of_isColimit hc ((mem_marked_sharpEdgeProdObj _ y).1 hy) with
        ⟨j, x, hx, hxy⟩ | ⟨v, hv⟩
      · exact ⟨j, (y.1, x), (mem_marked_sharpEdgeProdObj _ _).2 hx, Prod.ext rfl hxy⟩
      · obtain ⟨j, w, rfl⟩ := Types.jointly_surjective_of_isColimit
          (isColimitOfPreserves ((evaluation _ _).obj _)
            (isColimitOfPreserves MarkedPresheaf.forget hc)) v
        exact ⟨j, (y.1, (F.obj j).underlying.map (SimplexCategory.σ 0).op w),
          (mem_marked_sharpEdgeProdObj _ _).2 ((F.obj j).map_σ_mem_marked w),
          Prod.ext rfl ((SSet.σ_naturality_apply (MarkedPresheaf.forget.map (c.ι.app j)) 0 w).trans
            hv)⟩⟩⟩⟩⟩

private theorem nonempty_invStruct_δ_zero_iff {Q : SSet.{u}} [Q.Quasicategory] (σ : Q _⦋2⦌)
    (h : Nonempty (Edge.mk' (Q.δ 2 σ)).InvStruct) :
    Nonempty (Edge.mk' (Q.δ 0 σ)).InvStruct ↔ Nonempty (Edge.mk' (Q.δ 1 σ)).InvStruct :=
  ⟨SSet.nonempty_invStruct_δ_one σ h, SSet.nonempty_invStruct_δ_zero σ h⟩

private theorem nonempty_invStruct_app_tensor {Q K : SSet.{u}} [Q.Quasicategory]
    (g : Δ[1] ⊗ K ⟶ Q)
    (b : K _⦋1⦌) (h₀ : Nonempty (Edge.mk' (g.app _
      ((Δ[1].σ 0 (Δ[1].δ 1 stdEdge), b) : (Δ[1] ⊗ K : SSet) _⦋1⦌))).InvStruct)
    (hv : ∀ (a : (Δ[1] : SSet.{u}) _⦋1⦌) (k : K _⦋0⦌),
      Nonempty (Edge.mk' (g.app _ ((a, K.σ 0 k) : (Δ[1] ⊗ K : SSet) _⦋1⦌))).InvStruct)
    (a : (Δ[1] : SSet.{u}) _⦋1⦌) :
    Nonempty (Edge.mk' (g.app _ ((a, b) : (Δ[1] ⊗ K : SSet) _⦋1⦌))).InvStruct := by
  let P : (Δ[1] : SSet.{u}) _⦋1⦌ → K _⦋1⦌ → Prop := fun a b ↦
    Nonempty (Edge.mk' (g.app _ ((a, b) : (Δ[1] ⊗ K : SSet) _⦋1⦌))).InvStruct
  have hδ (i : Fin 3) (x : (Δ[1] : SSet.{u}) _⦋2⦌) (y : K _⦋2⦌) :
      Q.δ i (g.app _ ((x, y) : (Δ[1] ⊗ K : SSet) _⦋2⦌)) =
        g.app _ ((Δ[1].δ i x, K.δ i y) : (Δ[1] ⊗ K : SSet) _⦋1⦌) :=
    (δ_naturality_apply g i _).symm
  have hP {a a' : (Δ[1] : SSet.{u}) _⦋1⦌} {b b' : K _⦋1⦌} (ha : a = a') (hb : b = b')
      (h : P a b) : P a' b' := ha ▸ hb ▸ h
  have F₁ (a : (Δ[1] : SSet.{u}) _⦋1⦌) (b : K _⦋1⦌) (h₂ : P (Δ[1].σ 0 (Δ[1].δ 1 a)) b)
      (h₀ : P a (K.σ 0 (K.δ 0 b))) : P a b := by
    have := nonempty_invStruct_δ_zero_iff
      (g.app _ ((Δ[1].σ 0 a, K.σ 1 b) : (Δ[1] ⊗ K : SSet) _⦋2⦌))
    rw [hδ, hδ, hδ] at this
    refine hP (δ_comp_σ_succ_apply (i := 0) a) (δ_comp_σ_self_apply (i := 1) b)
      ((this (hP (δ_comp_σ_of_gt_apply (i := 1) (j := 0) (by decide) a).symm
        (δ_comp_σ_succ_apply (i := 1) b).symm h₂)).1
      (hP (δ_comp_σ_self_apply (i := 0) a).symm
        (δ_comp_σ_of_le_apply (i := 0) (j := 0) (by decide) b).symm h₀))
  have F₂ (a : (Δ[1] : SSet.{u}) _⦋1⦌) (b : K _⦋1⦌) (h₂ : P a (K.σ 0 (K.δ 1 b))) (h₁ : P a b) :
      P (Δ[1].σ 0 (Δ[1].δ 0 a)) b := by
    have := nonempty_invStruct_δ_zero_iff
      (g.app _ ((Δ[1].σ 1 a, K.σ 0 b) : (Δ[1] ⊗ K : SSet) _⦋2⦌))
    rw [hδ, hδ, hδ] at this
    refine hP (δ_comp_σ_of_le_apply (i := 0) (j := 0) (by decide) a)
      (δ_comp_σ_self_apply (i := 0) b)
      ((this (hP (δ_comp_σ_succ_apply (i := 1) a).symm
        (δ_comp_σ_of_gt_apply (i := 1) (j := 0) (by decide) b).symm h₂)).2
      (hP (δ_comp_σ_self_apply (i := 1) a).symm (δ_comp_σ_succ_apply (i := 0) b).symm h₁))
  have h₁ : P stdEdge b := F₁ _ b h₀ (hv _ _)
  have e (x y : (Δ[1] : SSet.{u}) _⦋1⦌) (h₀ : x 0 = y 0) (h₁ : x 1 = y 1) : x = y :=
    stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> assumption
  rcases stdSimplex.edge_one_cases a with rfl | rfl | rfl
  · exact hP (by exact e _ _ rfl rfl) rfl h₀
  · exact hP (by exact e _ _ rfl rfl) rfl h₁
  · exact hP (by exact e _ _ rfl rfl) rfl (F₂ _ b (hv _ _) h₁)

private theorem stdSimplex_zero_eq {k : ℕ} (x y : (Δ[0] : SSet.{u}) _⦋k⦌) : x = y :=
  stdSimplex.ext _ _ fun _ ↦ Subsingleton.elim (α := Fin 1) _ _

private theorem trivialCofibrations_sharpEdgeEndpoint_app_flat_stdSimplex_zero :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      ((sharpEdgeEndpoint 0).app ((MarkedPresheaf.flat edgeMarking).obj Δ[0])) := by
  refine ⟨(MarkedPresheaf.mono_iff _).2
    (SplitMono.mono ⟨CartesianMonoidalCategory.snd _ _, CartesianMonoidalCategory.lift_snd _ _⟩),
    (weakEquivalence_iff _).1 (weakEquivalence_of_hasLiftingProperty
      ((sharpEdgeEndpoint 0).app ((MarkedPresheaf.flat edgeMarking).obj Δ[0]))
      fun E B p hE hB hp ↦ ⟨fun {u v} sq ↦ ?_⟩)⟩
  obtain ⟨hEq, hEn⟩ := (MarkedSSet.modelCategoryCartesian.isFibrant_iff E).1 hE
  obtain ⟨hBq, hBn⟩ := (MarkedSSet.modelCategoryCartesian.isFibrant_iff B).1 hB
  have : SSet.Quasicategory (MarkedPresheaf.forget.obj E) := hEq
  have : SSet.Quasicategory (MarkedPresheaf.forget.obj B) := hBq
  have : Isofibration (MarkedPresheaf.forget.map p) :=
    (MarkedSSet.modelCategoryCartesian.fibration_iff_isofibration p).1 hp
  let F := MarkedPresheaf.forget (D := edgeMarking)
  let pt : (Δ[0] : SSet.{u}) _⦋0⦌ := stdSimplex.obj₀Equiv.symm 0
  let e₁ : (Δ[1] ⊗ Δ[0] : SSet.{u}) _⦋1⦌ := (stdEdge, Δ[0].σ 0 pt)
  have hv0 : ((F.map ((sharpEdgeEndpoint 0).app ((MarkedPresheaf.flat edgeMarking).obj Δ[0]))).app
      _ pt : (Δ[1] ⊗ Δ[0] : SSet.{u}) _⦋0⦌) =
      (Δ[1] ⊗ Δ[0] : SSet.{u}).δ 1 e₁ :=
    Prod.ext (stdSimplex.ext _ _ fun a ↦ by fin_cases a; rfl) (stdSimplex_zero_eq _ _)
  have hsrc : SimplicialObject.δ B.underlying 1 ((F.map v).app _ e₁) =
      (F.map p).app _ ((F.map u).app _ pt) :=
    (δ_naturality_apply (F.map v) 1 e₁).symm.trans ((congrArg ((F.map v).app _) hv0.symm).trans
      (ConcreteCategory.congr_hom (congr_app (congrArg F.map sq.w) _) pt).symm)
  have he : Nonempty (Edge.mk' ((F.map v).app _ e₁)).InvStruct :=
    (hBn _).1 (MarkedPresheaf.map_mem_marked v ((mem_marked_sharpEdgeProdObj
      ((MarkedPresheaf.flat edgeMarking).obj Δ[0]) e₁).2
      (MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj Δ[0]) pt)))
  obtain ⟨x₁, f, ⟨hf⟩, hfe⟩ := Isofibration.exists_lift (p := MarkedPresheaf.forget.map p)
    ((F.map u).app _ pt) ((Edge.mk' ((F.map v).app _ e₁)).ofEq hsrc rfl) ⟨he.some.ofEq rfl⟩
  have hfs : (SSet.yonedaEquiv.symm f.edge).app _ stdEdge = f.edge :=
    (app_stdEdge _).trans (Equiv.apply_symm_apply _ _)
  let ℓ : sharpEdgeProdObj ((MarkedPresheaf.flat edgeMarking).obj Δ[0]) ⟶ E :=
    edgeHomMk (CartesianMonoidalCategory.fst _ _ ≫ SSet.yonedaEquiv.symm f.edge)
      fun ⟨a, b⟩ _ ↦ by
        change (SSet.yonedaEquiv.symm f.edge).app _ a ∈ E.marked ⦋1⦌
        obtain rfl | rfl | rfl : a = Δ[1].σ 0 (Δ[1].δ 1 stdEdge) ∨ a = stdEdge ∨
            a = Δ[1].σ 0 (Δ[1].δ 0 stdEdge) := by
          rcases stdSimplex.edge_one_cases a with rfl | rfl | rfl <;>
            [left; (right; left); (right; right)] <;> exact stdSimplex.ext _ _ fun t ↦ by
              fin_cases t <;> rfl
        · exact (congrArg (· ∈ E.marked ⦋1⦌)
            (σ_naturality_apply (SSet.yonedaEquiv.symm f.edge) 0 _)).mpr (E.map_σ_mem_marked _)
        · exact (congrArg (· ∈ E.marked ⦋1⦌) hfs).mpr ((hEn _).2 ⟨hf.ofEq rfl⟩)
        · exact (congrArg (· ∈ E.marked ⦋1⦌)
            (σ_naturality_apply (SSet.yonedaEquiv.symm f.edge) 0 _)).mpr (E.map_σ_mem_marked _)
  have hpt {Y : SSet.{u}} (g : Δ[0] ⟶ Y) : SSet.yonedaEquiv g = g.app _ pt :=
    congrArg (g.app _) (stdSimplex_zero_eq _ _)
  let s : Δ[1] ⟶ (Δ[1] ⊗ Δ[0] : SSet.{u}) :=
    CartesianMonoidalCategory.lift (𝟙 _) (stdSimplex.isTerminalObj₀.from _)
  have hse : s.app _ stdEdge = e₁ := Prod.ext rfl (stdSimplex_zero_eq _ _)
  have key : s ≫ F.map (ℓ ≫ p) = s ≫ F.map v := by
    rw [Functor.map_comp]
    exact SSet.yonedaEquiv.injective ((app_stdEdge (s ≫ F.map ℓ ≫ F.map p)).symm.trans (Eq.trans
      ((congrArg (fun z ↦ (F.map p).app _ ((F.map ℓ).app _ z)) hse).trans
        ((congrArg ((F.map p).app _) hfs).trans (hfe.trans
          (congrArg ((F.map v).app _) hse.symm)))) (app_stdEdge (s ≫ F.map v))))
  refine ⟨⟨⟨ℓ, MarkedPresheaf.hom_ext (SSet.yonedaEquiv.injective ((hpt _).trans
    (Eq.trans ?_ (hpt _).symm))), MarkedPresheaf.hom_ext ?_⟩⟩⟩
  · refine (congrArg ((F.map ℓ).app _) hv0).trans ?_
    refine (δ_naturality_apply (F.map ℓ) 1 e₁).trans ?_
    exact (congrArg (SimplicialObject.δ E.underlying 1) hfs).trans f.src_eq
  · ext ⟨⟨k⟩⟩ ⟨z₁, z₂⟩
    have hz : ((z₁, z₂) : (Δ[1] ⊗ Δ[0] : SSet.{u}) _⦋k⦌) = s.app _ z₁ :=
      Prod.ext rfl (stdSimplex_zero_eq z₂ _)
    have h1 := congrArg (fun w ↦ (F.map (ℓ ≫ p)).app _ w) hz
    have h2 := congrArg (fun w ↦ (F.map v).app _ w) hz
    have h3 := ConcreteCategory.congr_hom (congr_app key (Opposite.op ⦋k⦌)) z₁
    refine h1.trans (Eq.trans ?_ h2.symm)
    exact h3

private theorem const_app_obj₀Equiv_symm_zero (K : SSet.{u}) (x : K _⦋1⦌) :
    (SSet.const (stdSimplex.obj₀Equiv.symm 0) : K ⟶ Δ[1]).app _ x =
      Δ[1].σ 0 (Δ[1].δ 1 stdEdge) :=
  stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl

private theorem trivialCofibrations_leibnizBox_of_isIso_forget {X Y : MarkedSSet.{u}} (f : X ⟶ Y)
    [IsIso (MarkedPresheaf.forget.map f)] :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (NatTrans.leibnizBox (sharpEdgeEndpoint 0) f) := by
  have : IsIso (MarkedPresheaf.forget.map (NatTrans.leibnizBox (sharpEdgeEndpoint 0) f)) :=
    MarkedPresheaf.forget.isIso_map_of_isPushout' (IsPushout.of_hasPushout _ _)
      (inferInstanceAs (IsIso (MarkedPresheaf.forget.map f))) _ (by
        rw [NatTrans.inl_leibnizBox]
        exact inferInstanceAs (IsIso (Δ[1] ◁ MarkedPresheaf.forget.map f)))
  refine ⟨(MarkedPresheaf.mono_iff _).2 inferInstance, (weakEquivalence_iff _).1
    (weakEquivalence_of_isIso_forget_map _ fun F _ g hg e he ↦ ?_)⟩
  have hc {x y : (Δ[1] ⊗ Y.underlying : SSet) _⦋1⦌} (h : x = y)
      (hx : Nonempty (Edge.mk' (g.app _ x)).InvStruct) :
      Nonempty (Edge.mk' (g.app _ y)).InvStruct :=
    h ▸ hx
  have hinl := (Functor.map_comp _ _ _).symm.trans (congrArg MarkedPresheaf.forget.map
    (NatTrans.inl_leibnizBox (sharpEdgeEndpoint 0) f))
  have hinr := (Functor.map_comp _ _ _).symm.trans (congrArg MarkedPresheaf.forget.map
    (NatTrans.inr_leibnizBox (sharpEdgeEndpoint 0) f))
  have hb : e.2 ∈ Y.marked ⦋1⦌ := (mem_marked_sharpEdgeProdObj Y e).1 he
  refine nonempty_invStruct_app_tensor g e.2 ?_ (fun a k ↦ ?_) e.1
  · refine hc ?_ (hg _ (MarkedPresheaf.map_mem_marked (pushout.inr _ _) hb))
    refine (ConcreteCategory.congr_hom (congr_app hinr _) e.2).trans ?_
    exact Prod.ext (const_app_obj₀Equiv_symm_zero Y.underlying e.2) rfl
  · obtain ⟨k', rfl⟩ : ∃ k', (MarkedPresheaf.forget.map f).app _ k' = k :=
      ⟨(inv (MarkedPresheaf.forget.map f)).app _ k,
        ConcreteCategory.congr_hom
          (congr_app (IsIso.inv_hom_id (MarkedPresheaf.forget.map f)) _) k⟩
    let x : (Δ[1] ⊗ X.underlying : SSet) _⦋1⦌ := (a, X.underlying.map (SimplexCategory.σ 0).op k')
    refine hc ?_ (hg _ (MarkedPresheaf.map_mem_marked (pushout.inl _ _)
      ((mem_marked_sharpEdgeProdObj X x).2 (X.map_σ_mem_marked k'))))
    refine (ConcreteCategory.congr_hom (congr_app hinl _) x).trans ?_
    exact Prod.ext rfl (σ_naturality_apply (MarkedPresheaf.forget.map f) 0 k')

private theorem trivialCofibrations_leibnizBox_sharpEdgeEndpoint_of_boundary
    (h : ∀ n : ℕ, cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (NatTrans.leibnizBox (sharpEdgeEndpoint 0) ((MarkedPresheaf.flat edgeMarking).map
        (∂Δ[n] : SSet.Subcomplex _).ι)))
    {K L : MarkedSSet.{u}} (i : K ⟶ L) [Mono i] :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (NatTrans.leibnizBox (sharpEdgeEndpoint 0) i) := by
  have := cartesianCylinder.{u}.isSaturated_trivialCofibrations cartesianGenerators
    cartesianGenerators_le_monomorphisms
  have := NatTrans.isSaturated_leibnizPreimage (sharpEdgeEndpoint 0)
    (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators)
  have : PreservesColimitsOfSize.{u, u} (MarkedPresheaf.flat edgeMarking) :=
    (MarkedPresheaf.flatForgetAdjunction edgeMarking).leftAdjoint_preservesColimits
  let C := NatTrans.leibnizPreimage (sharpEdgeEndpoint 0)
    (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators)
  have hflat : monomorphisms SSet.{u} ≤ C.inverseImage (MarkedPresheaf.flat edgeMarking) := by
    rw [← saturation_I_eq_monomorphisms]
    refine saturation_le _ _ ?_
    rintro _ _ _ ⟨n⟩
    exact h n
  let E : Set (L.underlying _⦋1⦌) :=
    {y | ∃ x ∈ K.marked ⦋1⦌, (MarkedPresheaf.forget.map i).app _ x = y}
  let i₀ : K ⟶ MarkedSSet.ofEdgeSet L.underlying E :=
    edgeHomMk (MarkedPresheaf.forget.map i) fun x hx ↦
      (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl ⟨x, hx, rfl⟩)
  let e : MarkedSSet.ofEdgeSet L.underlying E ⟶ L := edgeHomMk (𝟙 _) fun y hy ↦ by
    rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ _).1 hy with ⟨x, hx, rfl⟩ | ⟨v, rfl⟩
    · exact MarkedPresheaf.map_mem_marked i hx
    · exact L.map_σ_mem_marked v
  have : IsIso (MarkedPresheaf.forget.map e) := inferInstanceAs (IsIso (𝟙 L.underlying))
  have he : C e := trivialCofibrations_leibnizBox_of_isIso_forget e
  let cK : (MarkedPresheaf.flat edgeMarking).obj K.underlying ⟶ K := edgeHomMk (𝟙 _)
    fun x hx ↦ by
      obtain ⟨v, rfl⟩ := exists_eq_σ_of_mem_marked_flat x hx
      exact K.map_σ_mem_marked v
  let d : (MarkedPresheaf.flat edgeMarking).obj L.underlying ⟶
      MarkedSSet.ofEdgeSet L.underlying E := edgeHomMk (𝟙 _) fun x hx ↦ by
    obtain ⟨v, rfl⟩ := exists_eq_σ_of_mem_marked_flat x hx
    exact (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inr ⟨v, rfl⟩)
  have sq : IsPushout cK ((MarkedPresheaf.flat edgeMarking).map (MarkedPresheaf.forget.map i))
      i₀ d := by
    refine IsPushout.of_isColimit (c := PushoutCocone.mk (f := cK)
      (g := (MarkedPresheaf.flat edgeMarking).map (MarkedPresheaf.forget.map i)) i₀ d
      (MarkedPresheaf.hom_ext rfl)) (MarkedPresheaf.isColimitOfForget _ ?_ fun ⟨n⟩ y hy ↦ ?_)
    · exact (isColimitMapCoconePushoutCoconeEquiv MarkedPresheaf.forget _).symm
        (IsPushout.id_vert (MarkedPresheaf.forget.map i)).flip.isColimit
    · obtain rfl : n = 1 := MarkedSSet.len_eq_one_of_mem_marked _ hy
      rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ _).1 hy with ⟨x, hx, rfl⟩ | ⟨v, rfl⟩
      · exact ⟨WalkingSpan.left, x, hx, rfl⟩
      · exact ⟨WalkingSpan.right, L.underlying.map (SimplexCategory.σ 0).op v,
          MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj L.underlying) v, rfl⟩
  have hi₀ : C i₀ := MorphismProperty.of_isPushout sq
    (hflat _ (MarkedPresheaf.forget.map_mono i))
  have : i = i₀ ≫ e := MarkedPresheaf.hom_ext rfl
  rw [this]
  exact C.comp_mem _ _ hi₀ he

private theorem trivialCofibrations_sharpEdgeEndpoint_app_of_boundary
    (h : ∀ n : ℕ, cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (NatTrans.leibnizBox (sharpEdgeEndpoint 0) ((MarkedPresheaf.flat edgeMarking).map
        (∂Δ[n] : SSet.Subcomplex _).ι)))
    (X : MarkedSSet.{u}) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      ((sharpEdgeEndpoint 0).app X) := by
  have hX := trivialCofibrations_leibnizBox_sharpEdgeEndpoint_of_boundary h (initial.to X)
  have hb : IsInitial ((𝟭 MarkedSSet.{u}).obj (⊥_ MarkedSSet.{u})) := initialIsInitial
  have hG : IsInitial (sharpEdgeProd.obj (⊥_ MarkedSSet.{u})) :=
    IsInitial.isInitialObj _ _ initialIsInitial
  have : IsIso ((sharpEdgeEndpoint 0).app (⊥_ MarkedSSet.{u})) :=
    ⟨⟨hG.to _, hb.hom_ext _ _, hG.hom_ext _ _⟩⟩
  have := (IsPushout.of_hasPushout ((sharpEdgeEndpoint 0).app (⊥_ MarkedSSet.{u}))
    ((𝟭 MarkedSSet.{u}).map (initial.to X))).isIso_inr_of_isIso
  rw [← NatTrans.inr_leibnizBox (sharpEdgeEndpoint 0) (initial.to X)]
  exact (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).comp_mem _ _
    ⟨monomorphisms.infer_property _, (weakEquivalences MarkedSSet.{u}).of_isIso _⟩ hX

section Boundary

private theorem horn_one_zero_apply {m : ℕ} (z : (Λ[1, 0] : SSet.{u}) _⦋m⦌) (a : Fin (m + 1)) :
    z.val a = 0 := by
  obtain ⟨j, hj, hjz⟩ := (mem_horn_iff_notMem_range z.val 0).1 z.2
  have two : ∀ x y : Fin 2, y ≠ 0 → x ≠ y → x = 0 := by decide
  exact two (z.val a) j hj fun h' ↦ hjz ⟨a, h'⟩

theorem stdSimplex_eq_σ_δ_of_apply_eq {k : ℕ} (z : (Δ[k] : SSet.{u}) _⦋1⦌) (h : z 0 = z 1) :
    z = Δ[k].σ 0 (Δ[k].δ 1 z) :=
  stdSimplex.ext _ _ fun a ↦ by
    fin_cases a
    exacts [rfl, h.symm]

variable (n : ℕ)

private def hornOneZeroVertex : (Λ[1, 0] : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm 0, by
    rw [mem_horn_iff_notMem_range]
    exact ⟨1, by decide, fun ⟨a, ha⟩ ↦ absurd ha (by fin_cases a; decide)⟩⟩

private def hornOneZeroTensorIso (Z : SSet.{u}) : (Λ[1, 0] : SSet.{u}) ⊗ Z ≅ Z where
  hom := CartesianMonoidalCategory.snd _ _
  inv := CartesianMonoidalCategory.lift (SSet.const hornOneZeroVertex) (𝟙 Z)
  hom_inv_id := by
    ext ⟨⟨k⟩⟩ ⟨z₁, z₂⟩
    · exact (Subtype.ext (stdSimplex.ext _ _ fun a ↦ (horn_one_zero_apply z₁ a).symm) :
        (SSet.const hornOneZeroVertex).app _ z₂ = z₁)
    · rfl
  inv_hom_id := CartesianMonoidalCategory.lift_snd _ _

private noncomputable def unionProdBase :
    (Δ[n] : SSet.{u}) ⟶ (Subcomplex.unionProd Λ[1, 0] ∂Δ[n] : SSet.{u}) :=
  (hornOneZeroTensorIso Δ[n]).inv ≫ Subcomplex.unionProd.ι₂ _ _

private theorem isPushout_unionProd :
    IsPushout (CartesianMonoidalCategory.lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 _) :
      (∂Δ[n] : SSet.{u}) ⟶ Δ[1] ⊗ ∂Δ[n]) (∂Δ[n]).ι (Subcomplex.unionProd.ι₁ _ _)
      (unionProdBase n) := by
  refine (Subcomplex.unionProd.isPushout Λ[1, 0] ∂Δ[n]).of_iso (hornOneZeroTensorIso _)
    (Iso.refl _) (hornOneZeroTensorIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · ext ⟨⟨k⟩⟩ ⟨z₁, z₂⟩
    · exact congrArg Fin.val (horn_one_zero_apply z₁ _)
    · rfl
  · exact CartesianMonoidalCategory.whiskerLeft_snd _ _
  · simp
  · simp [unionProdBase]

private noncomputable abbrev markedUnionProd : MarkedSSet.{u} :=
  (overMarking _ (verticalEdges n)).obj (Over.mk (Subcomplex.unionProd Λ[1, 0] ∂Δ[n]).ι)

private noncomputable def markedUnionProdInl :
    sharpEdgeProd.obj ((MarkedPresheaf.flat edgeMarking).obj ∂Δ[n]) ⟶ markedUnionProd n :=
  edgeHomMk (Subcomplex.unionProd.ι₁ _ _) fun e he ↦ by
    obtain ⟨w, hw⟩ := exists_eq_σ_of_mem_marked_flat _
      ((mem_marked_sharpEdgeProdObj ((MarkedPresheaf.flat edgeMarking).obj ∂Δ[n]) e).1 he)
    refine (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl ?_)
    change ((∂Δ[n]).ι.app _ e.2) 0 = ((∂Δ[n]).ι.app _ e.2) 1
    rw [hw]
    rfl

private noncomputable def markedUnionProdInr :
    (MarkedPresheaf.flat edgeMarking).obj Δ[n] ⟶ markedUnionProd n :=
  edgeHomMk (unionProdBase n) fun e he ↦ by
    obtain ⟨w, rfl⟩ := exists_eq_σ_of_mem_marked_flat e he
    exact (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl rfl)

private theorem isPushout_markedUnionProd :
    IsPushout ((sharpEdgeEndpoint 0).app ((MarkedPresheaf.flat edgeMarking).obj ∂Δ[n]))
      ((𝟭 MarkedSSet.{u}).map ((MarkedPresheaf.flat edgeMarking).map (∂Δ[n]).ι))
      (markedUnionProdInl n) (markedUnionProdInr n) := by
  have hc := (isColimitMapCoconePushoutCoconeEquiv MarkedPresheaf.forget
    (MarkedPresheaf.hom_ext (isPushout_unionProd n).w :
      (sharpEdgeEndpoint 0).app ((MarkedPresheaf.flat edgeMarking).obj ∂Δ[n]) ≫
        markedUnionProdInl n = (𝟭 MarkedSSet.{u}).map
          ((MarkedPresheaf.flat edgeMarking).map (∂Δ[n]).ι) ≫ markedUnionProdInr n)).symm
    (isPushout_unionProd n).isColimit
  refine IsPushout.of_isColimit (MarkedPresheaf.isColimitOfForget _ hc fun ⟨k⟩ y hy ↦ ?_)
  obtain rfl : k = 1 := MarkedSSet.len_eq_one_of_mem_marked _ hy
  have hv : (Subcomplex.unionProd Λ[1, 0] ∂Δ[n]).ι.app _ y ∈ verticalEdges n := by
    rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ y).1 hy with hy | ⟨v, rfl⟩
    exacts [hy, rfl]
  obtain ⟨⟨y₁, y₂⟩, hyU⟩ := y
  have hy₂ : y₂ = Δ[n].σ 0 (Δ[n].δ 1 y₂) := stdSimplex_eq_σ_δ_of_apply_eq y₂ hv
  rcases (Subcomplex.mem_unionProd_iff _ _ _).1 hyU with h2 | h1
  · refine ⟨WalkingSpan.left, ((y₁, ⟨y₂, h2⟩) : (Δ[1] ⊗ ∂Δ[n] : SSet.{u}) _⦋1⦌),
      (mem_marked_sharpEdgeProdObj _ _).2 ?_, rfl⟩
    have h : (⟨y₂, h2⟩ : (∂Δ[n] : SSet.{u}) _⦋1⦌) =
        (∂Δ[n] : SSet.{u}).σ 0 ((∂Δ[n] : SSet.{u}).δ 1 ⟨y₂, h2⟩) := Subtype.ext hy₂
    rw [h]
    exact MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj ∂Δ[n]) _
  · refine ⟨WalkingSpan.right, y₂, ?_, Subtype.ext (Prod.ext
      (stdSimplex.ext _ _ fun a ↦ (horn_one_zero_apply ⟨y₁, h1⟩ a).symm) rfl)⟩
    rw [hy₂]
    exact MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj Δ[n]) _

private noncomputable def sharpEdgeProdFlatIso :
    (overMarking _ (verticalEdges n)).obj (Over.mk (𝟙 (Δ[1] ⊗ Δ[n] : SSet.{u}))) ≅
      sharpEdgeProd.obj ((MarkedPresheaf.flat edgeMarking).obj Δ[n]) where
  hom := edgeHomMk (𝟙 _) fun e he ↦ by
    refine (mem_marked_sharpEdgeProdObj ((MarkedPresheaf.flat edgeMarking).obj Δ[n]) e).2 ?_
    rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ e).1 he with he | ⟨v, rfl⟩
    · rw [stdSimplex_eq_σ_δ_of_apply_eq e.2 he]
      exact MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj Δ[n]) _
    · exact MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj Δ[n]) v.2
  inv := edgeHomMk (𝟙 _) fun e he ↦ by
    obtain ⟨w, hw⟩ := exists_eq_σ_of_mem_marked_flat _
      ((mem_marked_sharpEdgeProdObj ((MarkedPresheaf.flat edgeMarking).obj Δ[n]) e).1 he)
    refine (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl ?_)
    exact (congrArg (fun x : (Δ[n] : SSet.{u}) _⦋1⦌ ↦ x 0 = x 1) hw).mpr rfl
  hom_inv_id := MarkedPresheaf.hom_ext rfl
  inv_hom_id := MarkedPresheaf.hom_ext rfl

private theorem trivialCofibrations_leibnizBox_sharpEdgeEndpoint_flat_boundary :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (NatTrans.leibnizBox (sharpEdgeEndpoint 0)
        ((MarkedPresheaf.flat edgeMarking).map (∂Δ[n] : SSet.Subcomplex _).ι)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : PreservesColimitsOfSize.{u, u} (MarkedPresheaf.flat edgeMarking) :=
      (MarkedPresheaf.flatForgetAdjunction edgeMarking).leftAdjoint_preservesColimits
    have hK : IsInitial ((MarkedPresheaf.flat edgeMarking).obj (∂Δ[0] : SSet.{u})) :=
      IsInitial.isInitialObj _ _
        (Subcomplex.isInitialBot.ofIso (Subcomplex.eqToIso boundary_zero.symm))
    have hG : IsInitial (sharpEdgeProd.obj ((MarkedPresheaf.flat edgeMarking).obj ∂Δ[0])) :=
      IsInitial.isInitialObj _ _ hK
    have : IsIso ((sharpEdgeEndpoint 0).app ((MarkedPresheaf.flat edgeMarking).obj ∂Δ[0])) :=
      ⟨⟨hG.to _, hK.hom_ext _ _, hG.hom_ext _ _⟩⟩
    have := (IsPushout.of_hasPushout
      ((sharpEdgeEndpoint 0).app ((MarkedPresheaf.flat edgeMarking).obj ∂Δ[0]))
      ((𝟭 MarkedSSet.{u}).map ((MarkedPresheaf.flat edgeMarking).map
        (∂Δ[0] : SSet.Subcomplex _).ι))).isIso_inr_of_isIso
    have h := NatTrans.inr_leibnizBox (sharpEdgeEndpoint 0)
      ((MarkedPresheaf.flat edgeMarking).map (∂Δ[0] : SSet.Subcomplex _).ι)
    rw [← IsIso.eq_inv_comp] at h
    rw [h]
    exact (cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).comp_mem _ _
      ⟨monomorphisms.infer_property _, (weakEquivalences MarkedSSet.{u}).of_isIso _⟩
      trivialCofibrations_sharpEdgeEndpoint_app_flat_stdSimplex_zero
  · refine ((cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).arrow_mk_iso_iff
      (Arrow.isoMk (isPushout_markedUnionProd n).isoPushout (sharpEdgeProdFlatIso n) ?_)).1
      (trivialCofibrations_overMarking_map_unionProd_ι hn)
    refine (isPushout_markedUnionProd n).hom_ext ?_ ?_
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ NatTrans.leibnizBox _ _)
        (isPushout_markedUnionProd n).inl_isoPushout_hom).trans
          (NatTrans.inl_leibnizBox _ _))).trans (MarkedPresheaf.hom_ext rfl)
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ NatTrans.leibnizBox _ _)
        (isPushout_markedUnionProd n).inr_isoPushout_hom).trans
          (NatTrans.inr_leibnizBox _ _))).trans (MarkedPresheaf.hom_ext rfl)

theorem trivialCofibrations_leibnizBox_sharpEdgeEndpoint {K L : MarkedSSet.{u}} (i : K ⟶ L)
    [Mono i] :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (NatTrans.leibnizBox (sharpEdgeEndpoint 0) i) :=
  trivialCofibrations_leibnizBox_sharpEdgeEndpoint_of_boundary
    (fun n ↦ trivialCofibrations_leibnizBox_sharpEdgeEndpoint_flat_boundary (n := n)) i

theorem trivialCofibrations_sharpEdgeEndpoint_app (X : MarkedSSet.{u}) :
    cartesianCylinder.{u}.trivialCofibrations cartesianGenerators ((sharpEdgeEndpoint 0).app X) :=
  trivialCofibrations_sharpEdgeEndpoint_app_of_boundary
    trivialCofibrations_leibnizBox_sharpEdgeEndpoint_flat_boundary X

theorem weakEquivalence_sharpEdgeProj_app (X : MarkedSSet.{u}) :
    WeakEquivalence (sharpEdgeProj.app X) := by
  have h : (sharpEdgeEndpoint 0).app X ≫ sharpEdgeProj.app X = 𝟙 X :=
    MarkedPresheaf.hom_ext (CartesianMonoidalCategory.lift_snd
      (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 X.underlying))
  have : WeakEquivalence ((sharpEdgeEndpoint 0).app X) :=
    (weakEquivalence_iff _).2 (trivialCofibrations_sharpEdgeEndpoint_app X).2
  have : WeakEquivalence ((sharpEdgeEndpoint 0).app X ≫ sharpEdgeProj.app X) := by
    rw [h]
    exact (weakEquivalence_iff _).2 ((weakEquivalences MarkedSSet.{u}).id_mem _)
  exact weakEquivalence_of_precomp ((sharpEdgeEndpoint 0).app X) _

theorem weakEquivalence_sharpEdgeEndpoint_app (ε : Fin 2) (X : MarkedSSet.{u}) :
    WeakEquivalence ((sharpEdgeEndpoint ε).app X) := by
  have h : (sharpEdgeEndpoint ε).app X ≫ sharpEdgeProj.app X = 𝟙 X :=
    MarkedPresheaf.hom_ext (CartesianMonoidalCategory.lift_snd
      (SSet.const (stdSimplex.obj₀Equiv.symm ε)) (𝟙 X.underlying))
  have := weakEquivalence_sharpEdgeProj_app X
  have : WeakEquivalence ((sharpEdgeEndpoint ε).app X ≫ sharpEdgeProj.app X) := by
    rw [h]
    exact (weakEquivalence_iff _).2 ((weakEquivalences MarkedSSet.{u}).id_mem _)
  exact weakEquivalence_of_postcomp _ (sharpEdgeProj.app X)

end Boundary

theorem weakEquivalence_of_sharpEdgeHomotopy {X Y : MarkedSSet.{u}} (p : Y ⟶ X) (s : X ⟶ Y)
    (hs : s ≫ p = 𝟙 X) (H : sharpEdgeProd.obj Y ⟶ Y) {a b : Fin 2}
    (ha : (sharpEdgeEndpoint a).app Y ≫ H = 𝟙 Y) (hb : (sharpEdgeEndpoint b).app Y ≫ H = p ≫ s) :
    WeakEquivalence p := by
  have := weakEquivalence_sharpEdgeEndpoint_app a Y
  have := weakEquivalence_sharpEdgeEndpoint_app b Y
  have : WeakEquivalence ((sharpEdgeEndpoint a).app Y ≫ H) := by
    rw [ha]
    exact (weakEquivalence_iff _).2 ((weakEquivalences MarkedSSet.{u}).id_mem _)
  have := weakEquivalence_of_precomp ((sharpEdgeEndpoint a).app Y) H
  have hw : WeakEquivalence (p ≫ s) := by
    rw [← hb]
    infer_instance
  let R : RetractArrow p (p ≫ s) :=
    { i := Arrow.homMk (𝟙 _) s (Category.id_comp _)
      r := Arrow.homMk (𝟙 _) p ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
        ((congrArg (p ≫ ·) hs.symm).trans (Category.assoc _ _ _).symm)))
      retract := Arrow.hom_ext _ _ (Category.id_comp _) hs }
  exact (weakEquivalence_iff _).2
    ((weakEquivalences MarkedSSet.{u}).of_retract R ((weakEquivalence_iff _).1 hw))

end SharpEdge

end Atoms.Homotopical
