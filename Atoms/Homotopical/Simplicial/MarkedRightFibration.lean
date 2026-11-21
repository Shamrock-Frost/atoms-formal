import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianFibration
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianPrism
import Atoms.Homotopical.Simplicial.CartesianMonoidal

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Simplicial
open MonoidalCategory CartesianMonoidalCategory

universe w u

namespace Atoms.Homotopical

open MarkedPresheaf (forget)

open SSet in
inductive markedRightGenerators : MorphismProperty MarkedSSet.{u}
  | innerHorn {n : ℕ} (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
      markedRightGenerators ((MarkedPresheaf.flat edgeMarking).map Λ[n + 2, i].ι)
  | flatSharp : markedRightGenerators (MarkedSSet.flatSharp coherentIso.{u})
  | endpointMarking : markedRightGenerators
      (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])) □
        Arrow.mk (MarkedSSet.flatSharp Δ[1])).hom
  | endpointBoundary (n : ℕ) : markedRightGenerators
      (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])) □
        Arrow.mk ((MarkedPresheaf.flat edgeMarking).map ∂Δ[n].ι)).hom

def markedRightFibrations : MorphismProperty MarkedSSet.{u} := markedRightGenerators.rlp

section Generators

open SSet

private abbrev MarkedRightGeneratorIndex : Type :=
  (Σ n : ℕ, {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)}) ⊕ Option (Option ℕ)

private noncomputable def markedRightGeneratorArrow :
    MarkedRightGeneratorIndex → Arrow MarkedSSet.{u}
  | .inl ⟨n, p⟩ => Arrow.mk ((MarkedPresheaf.flat edgeMarking).map Λ[n + 2, p.1].ι)
  | .inr none => Arrow.mk (MarkedSSet.flatSharp coherentIso.{u})
  | .inr (some none) =>
      Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])) □
        Arrow.mk (MarkedSSet.flatSharp Δ[1])
  | .inr (some (some n)) =>
      Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])) □
        Arrow.mk ((MarkedPresheaf.flat edgeMarking).map ∂Δ[n].ι)

private theorem markedRightGenerators_eq_ofHoms :
    markedRightGenerators = ofHoms fun i => (markedRightGeneratorArrow.{u} i).hom := by
  ext X Y f
  constructor
  · rintro (⟨i, h0, hn⟩ | _ | _ | n)
    · exact ofHoms.mk (f := fun i => (markedRightGeneratorArrow i).hom)
        (Sum.inl ⟨_, i, h0, hn⟩ : MarkedRightGeneratorIndex)
    · exact ofHoms.mk (f := fun i => (markedRightGeneratorArrow i).hom)
        (Sum.inr none : MarkedRightGeneratorIndex)
    · exact ofHoms.mk (f := fun i => (markedRightGeneratorArrow i).hom)
        (Sum.inr (some none) : MarkedRightGeneratorIndex)
    · exact ofHoms.mk (f := fun i => (markedRightGeneratorArrow i).hom)
        (Sum.inr (some (some n)) : MarkedRightGeneratorIndex)
  · rintro ⟨(⟨n, i, h0, hn⟩ | _ | _ | n)⟩
    · exact markedRightGenerators.innerHorn i h0 hn
    · exact markedRightGenerators.flatSharp
    · exact markedRightGenerators.endpointMarking
    · exact markedRightGenerators.endpointBoundary n

instance isSmall_markedRightGenerators : markedRightGenerators.{u}.IsSmall.{w} := by
  rw [markedRightGenerators_eq_ofHoms]
  exact isSmall_ofHoms _

instance mono_sharp_map_δ_zero :
    Mono ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ (Δ[1] : SSet.{u}))) :=
  (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])))

instance mono_flatSharp (Z : SSet.{u}) : Mono (MarkedSSet.flatSharp Z) :=
  (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (𝟙 Z)))

theorem markedRightGenerators_le_monomorphisms :
    markedRightGenerators ≤ monomorphisms MarkedSSet.{u} := by
  rintro _ _ _ (⟨i, h0, hn⟩ | _ | _ | n)
  · exact (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono Λ[_ + 2, i].ι))
  · exact mono_flatSharp _
  · exact @MarkedSSet.mono_pushoutProduct _ _ mono_sharp_map_δ_zero (mono_flatSharp _)
  · exact @MarkedSSet.mono_pushoutProduct _ _ mono_sharp_map_δ_zero
      (inferInstanceAs (Mono ((MarkedPresheaf.flat edgeMarking).map
        (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι)))

end Generators

section Dictionaries

open SSet

variable {X A : MarkedSSet.{u}} (p : X ⟶ A)

private theorem innerFibration_of_hasLiftingProperty
    (h : ∀ {n : ℕ} (i : Fin (n + 3)), 0 < i → i < Fin.last (n + 2) →
      HasLiftingProperty ((MarkedPresheaf.flat edgeMarking).map Λ[n + 2, i].ι) p) :
    InnerFibration (forget.map p) :=
  ⟨fun _ _ _ ⟨i, h0, hn⟩ =>
    ((MarkedPresheaf.flatForgetAdjunction edgeMarking).hasLiftingProperty_iff _ _).1 (h i h0 hn)⟩

theorem hasLiftingProperty_flatSharp_iff (Z : SSet.{u}) :
    HasLiftingProperty (MarkedSSet.flatSharp Z) p ↔ ∀ g : Z ⟶ forget.obj X,
      (∀ e : Z _⦋1⦌, (g ≫ forget.map p).app _ e ∈ A.marked ⦋1⦌) →
        ∀ e : Z _⦋1⦌, g.app _ e ∈ X.marked ⦋1⦌ := by
  constructor
  · intro h g hg e
    let u : (MarkedPresheaf.flat edgeMarking).obj Z ⟶ X :=
      ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ _).symm g
    have sq : CommSq u (MarkedSSet.flatSharp Z) p (edgeHomMk (g ≫ forget.map p) fun e _ => hg e) :=
      ⟨MarkedPresheaf.hom_ext rfl⟩
    have hl : forget.map sq.lift = g := congrArg forget.map sq.fac_left
    exact hl ▸ MarkedPresheaf.map_mem_marked sq.lift
      ((MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl)
  · refine fun h => ⟨fun {u v} sq => ?_⟩
    have hv : forget.map u ≫ forget.map p = forget.map v :=
      (forget.map_comp _ _).symm.trans (congrArg forget.map sq.w)
    refine ⟨⟨⟨edgeHomMk (forget.map u) fun e _ => h _ (fun e => ?_) e,
      MarkedPresheaf.hom_ext rfl, MarkedPresheaf.hom_ext ((forget.map_comp _ _).trans hv)⟩⟩⟩
    have :=
      MarkedPresheaf.map_mem_marked v (x := e) ((MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl)
    exact (ConcreteCategory.congr_hom (congr_app hv _) e).symm ▸ this

end Dictionaries

section Box

open SSet

private theorem yonedaEquiv_symm_app_prod_σ {K : SSet.{u}} (v : K _⦋0⦌)
    (e : (Δ[1] : SSet.{u}) _⦋1⦌) :
    (yonedaEquiv.symm (show (Δ[1] ⊗ K : SSet.{u}) _⦋1⦌ from
      (yonedaEquiv (𝟙 Δ[1]), K.σ 0 v))).app _ e = ((e, K.σ 0 v) : (Δ[1] ⊗ K : SSet.{u}) _⦋1⦌) := by
  refine Prod.ext (stdSimplex.ext _ _ fun _ => rfl) ?_
  change K.map _ (K.map _ v) = K.map _ v
  rw [← Functor.map_comp_apply, ← op_comp]
  exact congrArg (fun g : ⦋1⦌ ⟶ ⦋0⦌ => K.map g.op v) (SimplexCategory.Hom.ext_one_left _ _
    (Subsingleton.elim (α := Fin 1) _ _) (Subsingleton.elim (α := Fin 1) _ _))

private theorem mem_marked_of_sharp_tensor_flat {K : SSet.{u}} {Y : MarkedSSet.{u}}
    (φ : Δ[1] ⊗ K ⟶ forget.obj Y)
    (hφ : ∀ v : K _⦋0⦌, φ.app _ (yonedaEquiv (𝟙 Δ[1]), K.σ 0 v) ∈ Y.marked ⦋1⦌)
    (e : (Δ[1] ⊗ K : SSet.{u}) _⦋1⦌)
    (he : e ∈ ((MarkedPresheaf.sharp edgeMarking).obj Δ[1] ⊗
      (MarkedPresheaf.flat edgeMarking).obj K).marked ⦋1⦌) : φ.app _ e ∈ Y.marked ⦋1⦌ := by
  obtain ⟨-, h₂⟩ := (MarkedSSet.mem_marked_tensor_iff ((MarkedPresheaf.sharp edgeMarking).obj Δ[1])
    ((MarkedPresheaf.flat edgeMarking).obj K) e).1 he
  obtain ⟨v, hv⟩ := exists_eq_σ_of_mem_marked_flat _ h₂
  have h := yonedaEquiv_symm_app_mem_marked (hφ v) e.1
  have hc : (yonedaEquiv.symm (φ.app _ (yonedaEquiv (𝟙 Δ[1]), K.σ 0 v))).app _ e.1 =
      φ.app _ (e.1, K.σ 0 v) := by
    rw [← yonedaEquiv_symm_app_prod_σ v e.1]
    exact (NatTrans.naturality_apply φ _ _).symm
  rw [show e = (e.1, K.σ 0 v) from Prod.ext rfl hv]
  exact hc ▸ h

private theorem mem_marked_of_sharp_zero_tensor_flat {L : SSet.{u}} {Y : MarkedSSet.{u}}
    (ψ : Δ[0] ⊗ L ⟶ forget.obj Y) (e : (Δ[0] ⊗ L : SSet.{u}) _⦋1⦌)
    (he : e ∈ ((MarkedPresheaf.sharp edgeMarking).obj Δ[0] ⊗
      (MarkedPresheaf.flat edgeMarking).obj L).marked ⦋1⦌) : ψ.app _ e ∈ Y.marked ⦋1⦌ := by
  obtain ⟨-, h₂⟩ := (MarkedSSet.mem_marked_tensor_iff ((MarkedPresheaf.sharp edgeMarking).obj Δ[0])
    ((MarkedPresheaf.flat edgeMarking).obj L) e).1 he
  obtain ⟨v, hv⟩ := exists_eq_σ_of_mem_marked_flat _ h₂
  have he' : e = (Δ[0] ⊗ L : SSet.{u}).σ 0 ((Δ[0] : SSet.{u}).δ 0 e.1, v) :=
    Prod.ext (yonedaEquiv.symm.injective (stdSimplex.isTerminalObj₀.hom_ext _ _)) hv
  rw [he']
  exact (σ_naturality_apply ψ (0 : Fin 1) _).symm ▸ MarkedSSet.map_σ_mem_marked _ _

variable {X A : MarkedSSet.{u}} (p : X ⟶ A)

private theorem exists_lift_of_hasLiftingProperty_box {K L : SSet.{u}} (i : K ⟶ L)
    (h : HasLiftingProperty
      (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])) □
        Arrow.mk ((MarkedPresheaf.flat edgeMarking).map i)).hom p)
    (a₁ : Δ[1] ⊗ K ⟶ forget.obj X) (a₂ : Δ[0] ⊗ L ⟶ forget.obj X) (b : Δ[1] ⊗ L ⟶ forget.obj A)
    (w : stdSimplex.δ 0 ▷ K ≫ a₁ = Δ[0] ◁ i ≫ a₂)
    (w₁ : a₁ ≫ forget.map p = Δ[1] ◁ i ≫ b) (w₂ : a₂ ≫ forget.map p = stdSimplex.δ 0 ▷ L ≫ b)
    (ha : ∀ v : K _⦋0⦌, a₁.app _ (yonedaEquiv (𝟙 Δ[1]), K.σ 0 v) ∈ X.marked ⦋1⦌)
    (hb : ∀ v : L _⦋0⦌, b.app _ (yonedaEquiv (𝟙 Δ[1]), L.σ 0 v) ∈ A.marked ⦋1⦌) :
    ∃ l : Δ[1] ⊗ L ⟶ forget.obj X, Δ[1] ◁ i ≫ l = a₁ ∧ stdSimplex.δ 0 ▷ L ≫ l = a₂ ∧
      l ≫ forget.map p = b ∧
        ∀ v : L _⦋0⦌, l.app _ (yonedaEquiv (𝟙 Δ[1]), L.σ 0 v) ∈ X.marked ⦋1⦌ := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]))
    ((MarkedPresheaf.flat edgeMarking).map i)
  let a₁' : (MarkedPresheaf.sharp edgeMarking).obj Δ[1] ⊗ (MarkedPresheaf.flat edgeMarking).obj K ⟶
      X := edgeHomMk a₁ (mem_marked_of_sharp_tensor_flat a₁ ha)
  let a₂' : (MarkedPresheaf.sharp edgeMarking).obj Δ[0] ⊗ (MarkedPresheaf.flat edgeMarking).obj L ⟶
      X := edgeHomMk a₂ (mem_marked_of_sharp_zero_tensor_flat a₂)
  let b' : (MarkedPresheaf.sharp edgeMarking).obj Δ[1] ⊗ (MarkedPresheaf.flat edgeMarking).obj L ⟶
      A := edgeHomMk b (mem_marked_of_sharp_tensor_flat b hb)
  let a := sq.isPushout.desc a₁' a₂' (MarkedPresheaf.hom_ext w)
  have csq : CommSq a sq.ι p b' := ⟨sq.isPushout.hom_ext
    (by
      rw [sq.isPushout.inl_desc_assoc, sq.inl_ι_assoc]
      exact MarkedPresheaf.hom_ext w₁)
    (by
      rw [sq.isPushout.inr_desc_assoc, sq.inr_ι_assoc]
      exact MarkedPresheaf.hom_ext w₂)⟩
  obtain ⟨l⟩ := (h.sq_hasLift csq).exists_lift
  have h₁ := congrArg forget.map ((sq.inl_ι_assoc l.l).symm.trans
    ((congrArg _ l.fac_left).trans (sq.isPushout.inl_desc _ _ _)))
  have h₂ := congrArg forget.map ((sq.inr_ι_assoc l.l).symm.trans
    ((congrArg _ l.fac_left).trans (sq.isPushout.inr_desc _ _ _)))
  refine ⟨forget.map l.l, (forget.map_comp _ _).symm.trans h₁,
    (forget.map_comp _ _).symm.trans h₂, (forget.map_comp _ _).symm.trans
      (congrArg forget.map l.fac_right), fun v => MarkedPresheaf.map_mem_marked l.l ?_⟩
  exact (MarkedSSet.mem_marked_tensor_iff _ _ _).2
    ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl,
      MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj L) v⟩

private theorem llp_box_flat {K L : SSet.{u}} (i : K ⟶ L) [Mono i] :
    markedRightFibrations.{u}.llp
      (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])) □
        Arrow.mk ((MarkedPresheaf.flat edgeMarking).map i)).hom := by
  let e := (MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ (Δ[1] : SSet.{u}))
  let α := (tensoringLeft MarkedSSet.{u}).map e
  have hiso {K' L' : MarkedSSet.{u}} (j : K' ⟶ L') :
      Arrow.mk (NatTrans.leibnizBox α j) ≅ (Arrow.mk e □ Arrow.mk j) :=
    NatTrans.leibnizBoxArrowIso α e (Iso.refl _) (Iso.refl _) (fun _ => by simp [α]) j
  have : PreservesColimitsOfSize.{u, u} (MarkedPresheaf.flat.{u} edgeMarking) :=
    (MarkedPresheaf.flatForgetAdjunction edgeMarking).leftAdjoint_preservesColimits
  have : IsSaturated.{u} (NatTrans.leibnizPreimage α markedRightFibrations.{u}.llp) :=
    NatTrans.isSaturated_leibnizPreimage α _
  have hI : SSet.modelCategoryQuillen.I ≤
      (NatTrans.leibnizPreimage α markedRightFibrations.{u}.llp).inverseImage
        (MarkedPresheaf.flat edgeMarking) := by
    rintro _ _ _ ⟨n⟩
    exact (MorphismProperty.arrow_mk_iso_iff _ (hiso _)).2
      (le_llp_rlp _ _ (markedRightGenerators.endpointBoundary n))
  have h := saturation_le _ _ hI
  rw [saturation_I_eq_monomorphisms] at h
  exact (MorphismProperty.arrow_mk_iso_iff _ (hiso _)).1 (h _ (monomorphisms.infer_property i))

private theorem isEmpty_boundary_zero (v : (∂Δ[0] : SSet.{u}) _⦋0⦌) : False := by
  have h := v.2
  simp [boundary_zero] at h

private theorem hom_ext_tensor_boundary_zero {Y Z : SSet.{u}} (f g : Y ⊗ (∂Δ[0] : SSet.{u}) ⟶ Z) :
    f = g := by
  ext n x
  have h := x.2.2
  simp [boundary_zero] at h

private theorem stdSimplex_zero_edge_eq (a b : (Δ[0] : SSet.{u}) _⦋1⦌) : a = b :=
  yonedaEquiv.symm.injective (stdSimplex.isTerminalObj₀.hom_ext _ _)

private theorem exists_mem_marked_of_markedRightFibrations (hp : markedRightFibrations p)
    (y : X.underlying _⦋0⦌) (f : A.underlying _⦋1⦌) (hf : f ∈ A.marked ⦋1⦌)
    (hfy : SimplicialObject.δ (A.underlying : SSet.{u}) 0 f = (forget.map p).app _ y) :
    ∃ f' : X.underlying _⦋1⦌, f' ∈ X.marked ⦋1⦌ ∧
      SimplicialObject.δ (X.underlying : SSet.{u}) 0 f' = y ∧
      (forget.map p).app _ f' = f := by
  have hy : yonedaEquiv.symm y ≫ forget.map p = stdSimplex.δ 0 ≫ yonedaEquiv.symm f := by
    exact (yonedaEquiv_symm_comp y _).trans ((congrArg yonedaEquiv.symm hfy.symm).trans
      (stdSimplex.δ_comp_yonedaEquiv_symm f 0).symm)
  obtain ⟨l, -, h₂, h₃, hl⟩ := exists_lift_of_hasLiftingProperty_box p (∂Δ[0]).ι
    (hp _ (markedRightGenerators.endpointBoundary 0))
    (snd _ _ ≫ (∂Δ[0]).ι ≫ yonedaEquiv.symm y) (fst _ _ ≫ yonedaEquiv.symm y)
    (fst _ _ ≫ yonedaEquiv.symm f) (hom_ext_tensor_boundary_zero _ _)
    (hom_ext_tensor_boundary_zero _ _)
    ((Category.assoc _ _ _).trans ((congrArg (fst _ _ ≫ ·) hy).trans
      (whiskerRight_fst_assoc _ _ _).symm))
    (fun v => (isEmpty_boundary_zero v).elim)
    (fun _ => (yonedaEquiv_symm_app_id f).symm ▸ hf)
  let c : Δ[1] ⟶ (Δ[1] ⊗ Δ[0] : SSet.{u}) := lift (𝟙 _) (stdSimplex.σ 0)
  have hc : stdSimplex.δ 0 ≫ c = lift (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ stdSimplex.δ 0 ▷ Δ[0] :=
    CartesianMonoidalCategory.hom_ext _ _ (by simp [c])
      (stdSimplex.isTerminalObj₀.hom_ext _ _)
  refine ⟨yonedaEquiv (c ≫ l), ?_, ?_, ?_⟩
  · have h := hl (yonedaEquiv (𝟙 Δ[0]))
    rwa [stdSimplex_zero_edge_eq (Δ[0].σ 0 _) (yonedaEquiv (stdSimplex.σ 0))] at h
  · have hm : stdSimplex.δ 0 ≫ c ≫ l = yonedaEquiv.symm y := by
      rw [← Category.assoc, hc, Category.assoc, h₂, lift_fst_assoc, Category.id_comp]
      rfl
    exact (stdSimplex.yonedaEquiv_δ_comp (c ≫ l) 0).symm.trans
      ((congrArg SSet.yonedaEquiv hm).trans (Equiv.apply_symm_apply _ _))
  · have hm : (c ≫ l) ≫ forget.map p = yonedaEquiv.symm f := by
      rw [Category.assoc, h₃, lift_fst_assoc, Category.id_comp]
      rfl
    exact (SSet.yonedaEquiv_comp (c ≫ l) (forget.map p)).symm.trans
      ((congrArg SSet.yonedaEquiv hm).trans (Equiv.apply_symm_apply _ _))

private theorem hornLastRetract_r_right_app (n : ℕ) (v : (Δ[n + 2] : SSet.{u}) _⦋0⦌) :
    (hornLastRetract.{u} n).r.right.app _ (yonedaEquiv (𝟙 Δ[1]), Δ[n + 2].σ 0 v) =
        Δ[n + 2].σ 0 v ∨
      (hornLastRetract.{u} n).r.right.app _ (yonedaEquiv (𝟙 Δ[1]), Δ[n + 2].σ 0 v) =
        Λ[n + 2, Fin.last (n + 2)].ι.app _ (horn.edge (n + 2) (Fin.last (n + 2))
          (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) (Fin.le_last _) (by simp)) := by
  obtain ⟨k, rfl⟩ := stdSimplex.obj₀Equiv.{u}.symm.surjective v
  by_cases hk : k = (Fin.last (n + 1)).castSucc
  · subst hk
    exact Or.inr ((congrArg SSet.yonedaEquiv
      (lift_const_last_comp_hornLastRetract_r_right.{u} n)).trans (Equiv.apply_symm_apply _ _))
  · exact Or.inl (congrArg SSet.yonedaEquiv (lift_const_comp_hornLastRetract_r_right.{u} n k hk))

private theorem isCartesianEdge_of_mem_marked (hp : markedRightFibrations p)
    {e : X.underlying _⦋1⦌} (he : e ∈ X.marked ⦋1⦌) :
    IsCartesianEdge (forget.map p) (yonedaEquiv.symm e) := by
  rw [isCartesianEdge_iff_hasLift_horn]
  intro n a b sq ha
  let R := hornLastRetract.{u} n
  let φ : Δ[0] ⟶ (Λ[1, 1] : SSet.{u}) := horn.ι 1 0 (by decide)
  let S := (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd Λ[n + 2, Fin.last (n + 2)]
  have hφ : φ ≫ Λ[1, 1].ι = stdSimplex.δ 0 := horn.ι_ι _ _ _
  have hr : R.r.left ≫ Λ[n + 2, Fin.last (n + 2)].ι = S.ι ≫ R.r.right := R.r_w
  have hi : R.i.left ≫ S.ι = Λ[n + 2, Fin.last (n + 2)].ι ≫ R.i.right := R.i_w
  have hS := Subcomplex.unionProd.isPushout (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex)
    Λ[n + 2, Fin.last (n + 2)]
  have hedge (v : (Δ[n + 2] : SSet.{u}) _⦋0⦌) :
      (R.r.right ≫ b).app _ (yonedaEquiv (𝟙 Δ[1]), Δ[n + 2].σ 0 v) ∈ A.marked ⦋1⦌ := by
    rcases hornLastRetract_r_right_app n v with h | h
    · refine (congrArg (b.app _) h).symm ▸ ?_
      exact (σ_naturality_apply b (0 : Fin 1) v).symm ▸ MarkedSSet.map_σ_mem_marked _ _
    · refine (congrArg (b.app _) h).symm ▸ ?_
      have hw := ConcreteCategory.congr_hom (congr_app sq.w _) (horn.edge (n + 2) (Fin.last (n + 2))
          (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) (Fin.le_last _) (by simp))
      refine hw ▸ ?_
      exact (congrArg ((forget.map p).app _) (ha.trans (Equiv.apply_symm_apply _ _))).symm ▸
        MarkedPresheaf.map_mem_marked p he
  have hedge' (v : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) _⦋0⦌) :
      (Subcomplex.unionProd.ι₁ _ _ ≫ R.r.left ≫ a).app _
        (yonedaEquiv (𝟙 Δ[1]), (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}).σ 0 v) ∈ X.marked ⦋1⦌ := by
    let x := (Subcomplex.unionProd.ι₁ _ _ ≫ R.r.left).app _
      (yonedaEquiv (𝟙 Δ[1]), (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}).σ 0 v)
    have hx : Λ[n + 2, Fin.last (n + 2)].ι.app _ x = R.r.right.app _
        (yonedaEquiv (𝟙 Δ[1]), Δ[n + 2].σ 0 (Λ[n + 2, Fin.last (n + 2)].ι.app _ v)) :=
      ConcreteCategory.congr_hom (congr_app ((Category.assoc _ _ _).trans
        ((congrArg (Subcomplex.unionProd.ι₁ _ _ ≫ ·) hr).trans
          (Subcomplex.unionProd.ι₁_ι_assoc _ _ _))) _) _
    change a.app _ x ∈ X.marked ⦋1⦌
    rcases hornLastRetract_r_right_app n (Λ[n + 2, Fin.last (n + 2)].ι.app _ v) with h | h
    · rw [show x = (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}).σ 0 v from
        Subtype.ext (hx.trans (h.trans (σ_naturality_apply _ (0 : Fin 1) v).symm))]
      exact (σ_naturality_apply a (0 : Fin 1) v).symm ▸ MarkedSSet.map_σ_mem_marked _ _
    · rw [show x = _ from Subtype.ext (hx.trans h), ha]
      exact (Equiv.apply_symm_apply SSet.yonedaEquiv e).symm ▸ he
  have ht : stdSimplex.isTerminalObj₀.from _ ≫ φ = 𝟙 _ := (cancel_mono Λ[1, 1].ι).1 (by
    rw [Category.assoc, hφ, horn_one_one_ι, Category.id_comp])
  obtain ⟨l, h₁, h₂, h₃, -⟩ := exists_lift_of_hasLiftingProperty_box p
    Λ[n + 2, Fin.last (n + 2)].ι (llp_box_flat _ p hp)
    (Subcomplex.unionProd.ι₁ _ _ ≫ R.r.left ≫ a)
    (φ ▷ _ ≫ Subcomplex.unionProd.ι₂ _ _ ≫ R.r.left ≫ a) (R.r.right ≫ b)
    (by rw [← hφ, comp_whiskerRight, Category.assoc, hS.w_assoc, whisker_exchange_assoc])
    (by rw [Category.assoc, Category.assoc, sq.w, reassoc_of% hr,
      Subcomplex.unionProd.ι₁_ι_assoc])
    (by rw [Category.assoc, Category.assoc, Category.assoc, sq.w, reassoc_of% hr,
      Subcomplex.unionProd.ι₂_ι_assoc, ← comp_whiskerRight_assoc, hφ])
    hedge' hedge
  have hl : S.ι ≫ l = R.r.left ≫ a := hS.hom_ext
    (by rw [Subcomplex.unionProd.ι₁_ι_assoc, h₁])
    (by rw [Subcomplex.unionProd.ι₂_ι_assoc, ← horn_one_one_ι, comp_whiskerRight_assoc, h₂,
      ← comp_whiskerRight_assoc, ht, id_whiskerRight, Category.id_comp])
  refine ⟨⟨⟨R.i.right ≫ l, ?_, ?_⟩⟩⟩
  · rw [← reassoc_of% hi, hl, R.retract_left_assoc]
    exact Category.id_comp _
  · rw [Category.assoc, h₃, R.retract_right_assoc]
    exact Category.id_comp _

end Box

section Square

open SSet

private def squareFun : Fin 2 × Fin 2 →o Fin 3 where
  toFun x := if x.2 = 1 then 2 else x.1.castSucc
  monotone' := by decide

private noncomputable def squareMap : Δ[1] ⊗ Δ[1] ⟶ (Δ[2] : SSet.{u}) :=
  (prodStdSimplex.isoNerve 1 1).hom ≫
    nerveMap (ULift.orderIso.symm.monotone.comp (squareFun.monotone.comp
      ULift.orderIso.monotone)).functor ≫ (stdSimplex.isoNerve 2).inv

private theorem lift_const_zero_comp_squareMap :
    lift (𝟙 Δ[1]) (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) ≫ squareMap.{u} =
      stdSimplex.δ 2 :=
  yonedaEquiv.injective (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)

private theorem lift_const_one_comp_squareMap :
    lift (𝟙 Δ[1]) (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) ≫ squareMap.{u} =
      stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋2⦌ 2) :=
  yonedaEquiv.injective (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)

private theorem whiskerRight_comp_squareMap :
    stdSimplex.δ 0 ▷ Δ[1] ≫ squareMap.{u} = snd _ _ ≫ stdSimplex.δ 0 := by
  have hs : snd _ _ ≫ lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) = 𝟙 (Δ[0] ⊗ Δ[1] : SSet.{u}) :=
    CartesianMonoidalCategory.hom_ext _ _ (stdSimplex.isTerminalObj₀.hom_ext _ _) (by simp)
  have he : lift (stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ 0) (𝟙 Δ[1]) ≫ squareMap.{u} =
      stdSimplex.δ 0 :=
    yonedaEquiv.injective (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)
  rw [← Category.id_comp (stdSimplex.δ 0 ▷ Δ[1] ≫ squareMap), ← hs, Category.assoc,
    lift_whiskerRight_assoc, he]

private theorem lift_const_zero_id_comp_squareMap :
    lift (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) (𝟙 Δ[1]) ≫ squareMap.{u} =
      stdSimplex.δ 1 :=
  yonedaEquiv.injective (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)

variable {X A : MarkedSSet.{u}} (p : X ⟶ A)

theorem mem_marked_δ_one_of_hasLiftingProperty
    (h : HasLiftingProperty
      (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])) □
        Arrow.mk (MarkedSSet.flatSharp Δ[1])).hom p) (σ : Δ[2] ⟶ forget.obj X)
    (h₂ : yonedaEquiv (stdSimplex.δ 2 ≫ σ) ∈ X.marked ⦋1⦌)
    (h₀ : yonedaEquiv (stdSimplex.δ 0 ≫ σ) ∈ X.marked ⦋1⦌)
    (hσ : ∀ e : (Δ[2] : SSet.{u}) _⦋1⦌, (σ ≫ forget.map p).app _ e ∈ A.marked ⦋1⦌) :
    yonedaEquiv (stdSimplex.δ 1 ≫ σ) ∈ X.marked ⦋1⦌ := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]))
    (MarkedSSet.flatSharp Δ[1])
  let τ := squareMap ≫ σ
  have hτ₁ (v : (Δ[1] : SSet.{u}) _⦋0⦌) :
      τ.app _ (yonedaEquiv (𝟙 Δ[1]), Δ[1].σ 0 v) ∈ X.marked ⦋1⦌ := by
    obtain ⟨k, rfl⟩ := stdSimplex.obj₀Equiv.{u}.symm.surjective v
    fin_cases k
    · refine MarkedSSet.mem_marked_of_eq ?_ h₂
      exact congrArg SSet.yonedaEquiv ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ σ) lift_const_zero_comp_squareMap.{u}))
    · refine MarkedSSet.mem_marked_of_eq ?_
        (MarkedSSet.map_σ_mem_marked X (σ.app _ (stdSimplex.obj₀Equiv.{u}.symm 2)))
      have e : SSet.yonedaEquiv (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋2⦌ 2) ≫ σ) =
          SimplicialObject.σ (forget.obj X : SSet.{u}) 0
            (σ.app _ (stdSimplex.obj₀Equiv.{u}.symm 2)) :=
        σ_naturality_apply (n := 0) σ 0 (stdSimplex.obj₀Equiv.{u}.symm 2)
      exact (congrArg SSet.yonedaEquiv ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ σ) lift_const_one_comp_squareMap.{u}))).trans e
  have hτ₂ (e : (Δ[0] ⊗ Δ[1] : SSet.{u}) _⦋1⦌) :
      (stdSimplex.δ 0 ▷ Δ[1] ≫ τ).app _ e ∈ X.marked ⦋1⦌ := by
    refine MarkedSSet.mem_marked_of_eq ?_ (yonedaEquiv_symm_app_mem_marked h₀ e.2)
    exact (congrArg (fun φ => φ.app _ e) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ σ) whiskerRight_comp_squareMap.{u}).trans (Category.assoc _ _ _)))).trans
        (congrArg (fun φ : Δ[1] ⟶ forget.obj X => φ.app _ e.2)
          (Equiv.symm_apply_apply SSet.yonedaEquiv (stdSimplex.δ 0 ≫ σ)).symm)
  let a : sq.pt ⟶ X := sq.isPushout.desc (edgeHomMk τ (mem_marked_of_sharp_tensor_flat τ hτ₁))
    (edgeHomMk (stdSimplex.δ 0 ▷ Δ[1] ≫ τ) fun e _ => hτ₂ e) (MarkedPresheaf.hom_ext rfl)
  have csq : CommSq a sq.ι p (edgeHomMk (Y := A) (τ ≫ forget.map p) fun e _ => hσ _) :=
    ⟨sq.isPushout.hom_ext
      (by
        rw [sq.isPushout.inl_desc_assoc, sq.inl_ι_assoc]
        exact MarkedPresheaf.hom_ext rfl)
      (by
        rw [sq.isPushout.inr_desc_assoc, sq.inr_ι_assoc]
        exact MarkedPresheaf.hom_ext rfl)⟩
  obtain ⟨l⟩ := (h.sq_hasLift csq).exists_lift
  have hl : forget.map l.l = τ := congrArg forget.map ((sq.inl_ι_assoc l.l).symm.trans
    ((congrArg _ l.fac_left).trans (sq.isPushout.inl_desc _ _ _)))
  have hm := MarkedPresheaf.map_mem_marked l.l
    (x := SSet.yonedaEquiv (lift (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) (𝟙 Δ[1])))
    ((MarkedSSet.mem_marked_tensor_iff _ _ _).2 ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl,
      (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl⟩)
  refine MarkedSSet.mem_marked_of_eq ?_ hm
  exact (congrArg SSet.yonedaEquiv ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ σ) lift_const_zero_id_comp_squareMap.{u}))).symm.trans
      (congrArg (fun φ : Δ[1] ⊗ Δ[1] ⟶ forget.obj X => φ.app _
        (SSet.yonedaEquiv (lift (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) (𝟙 Δ[1]))))
        hl.symm)

end Square

section OnlyIf

open SSet

variable {X A : MarkedSSet.{u}} (p : X ⟶ A)

private theorem mem_marked_app_stdSimplex_zero {Y : MarkedSSet.{u}} (v : Δ[0] ⟶ forget.obj Y)
    (e : (Δ[0] : SSet.{u}) _⦋1⦌) : v.app _ e ∈ Y.marked ⦋1⦌ := by
  rw [stdSimplex_zero_edge_eq e (Δ[0].σ 0 (Δ[0].δ 0 e))]
  exact (σ_naturality_apply v (0 : Fin 1) _).symm ▸ MarkedSSet.map_σ_mem_marked _ _

private theorem mem_marked_of_isCartesianEdge (hp : markedRightFibrations p)
    {e : X.underlying _⦋1⦌} (he : (forget.map p).app _ e ∈ A.marked ⦋1⦌)
    (hc : IsCartesianEdge (forget.map p) (yonedaEquiv.symm e)) : e ∈ X.marked ⦋1⦌ := by
  have := innerFibration_of_hasLiftingProperty p fun i h0 hn =>
    hp _ (markedRightGenerators.innerHorn i h0 hn)
  obtain ⟨f', hf', hf'y, hf'p⟩ := exists_mem_marked_of_markedRightFibrations p hp
    (SimplicialObject.δ (X.underlying : SSet.{u}) 0 e) _ he
    (δ_naturality_apply (forget.map p) (0 : Fin 2) e).symm
  have hf'c := isCartesianEdge_of_mem_marked p hp hf'
  obtain ⟨σ, hσ₀, hσ₁, hσp⟩ := exists_simplex_two_of_isCartesianEdge hf'c e
    (hf'y.symm.trans (congrArg _ (Equiv.apply_symm_apply SSet.yonedaEquiv f').symm))
    (SimplicialObject.σ (forget.obj A : SSet.{u}) 0 ((forget.map p).app _ e))
    ((δ_comp_σ_self_apply (n := 1) (0 : Fin 2) _).trans (hf'p.symm.trans
      (congrArg _ (Equiv.apply_symm_apply SSet.yonedaEquiv f').symm)))
    (δ_comp_σ_succ_apply (n := 1) (0 : Fin 2) _)
  obtain ⟨α, hα, ⟨I⟩⟩ := exists_invStruct_fiber_of_isCartesianEdge (forget.map p) σ
    (by rw [hσp]; exact (congrArg _ (δ_comp_σ_succ_apply (n := 1) (0 : Fin 2) _)).symm)
    (by rwa [hσ₀, Equiv.symm_apply_apply]) (by rwa [hσ₁])
  let v : Δ[0] ⟶ forget.obj A := yonedaEquiv.symm (SimplicialObject.δ (forget.obj A : SSet.{u}) 1
    (SimplicialObject.δ (forget.obj A : SSet.{u}) 1 ((forget.map p).app _ σ)))
  have : SSet.Quasicategory (pullback (forget.map p) v) :=
    quasicategory_of_innerFibration (pullback.snd _ _)
  obtain ⟨G, hG⟩ := exists_coherentIso_extension (Edge.mk' α) I
  have hα₂ := (hasLiftingProperty_flatSharp_iff p coherentIso).1
    (hp _ markedRightGenerators.flatSharp) (G ≫ pullback.fst (forget.map p) v) (fun e' => by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact mem_marked_app_stdSimplex_zero v ((G ≫ pullback.snd _ _).app _ e'))
    coherentIso.hom.edge
  have hα₂' : (G ≫ pullback.fst (forget.map p) v).app _ coherentIso.hom.edge =
      SimplicialObject.δ (forget.obj X : SSet.{u}) 2 σ :=
    (congrArg (fun z => (pullback.fst (forget.map p) v).app _ z) hG).trans hα
  have hδ (i : Fin 3) : SSet.yonedaEquiv (stdSimplex.δ i ≫ yonedaEquiv.symm σ) =
      SimplicialObject.δ (forget.obj X : SSet.{u}) i σ :=
    (congrArg SSet.yonedaEquiv (stdSimplex.δ_comp_yonedaEquiv_symm σ i)).trans
      (Equiv.apply_symm_apply _ _)
  refine MarkedSSet.mem_marked_of_eq
    ((hδ 1).trans hσ₁).symm (mem_marked_δ_one_of_hasLiftingProperty p
    (hp _ markedRightGenerators.endpointMarking) (yonedaEquiv.symm σ)
    (MarkedSSet.mem_marked_of_eq ((hδ 2).trans hα₂'.symm) hα₂)
    (MarkedSSet.mem_marked_of_eq ((hδ 0).trans (hσ₀.trans (Equiv.apply_symm_apply _ _))) hf')
    fun e' => ?_)
  refine MarkedSSet.mem_marked_of_eq (congrArg (fun φ : Δ[2] ⟶ forget.obj A => φ.app _ e')
    ((yonedaEquiv_symm_comp σ (forget.map p)).trans ((congrArg yonedaEquiv.symm hσp).trans
      (stdSimplex.σ_comp_yonedaEquiv_symm _ 0).symm))) ?_
  exact yonedaEquiv_symm_app_mem_marked he _

end OnlyIf

section If

open SSet

variable {X A : MarkedSSet.{u}} (p : X ⟶ A)

theorem mem_marked_of_isLocallyCartesianEdge [InnerFibration (forget.map p)]
    (h₂ : ∀ (y : X.underlying _⦋0⦌) (f : A.underlying _⦋1⦌), f ∈ A.marked ⦋1⦌ →
      SimplicialObject.δ (A.underlying : SSet.{u}) 0 f = (forget.map p).app _ y →
        ∃ f' : X.underlying _⦋1⦌, f' ∈ X.marked ⦋1⦌ ∧
          SimplicialObject.δ (X.underlying : SSet.{u}) 0 f' = y ∧ (forget.map p).app _ f' = f)
    (h₃ : ∀ f : X.underlying _⦋1⦌, f ∈ X.marked ⦋1⦌ ↔
      (forget.map p).app _ f ∈ A.marked ⦋1⦌ ∧ IsCartesianEdge (forget.map p) (yonedaEquiv.symm f))
    {f : Δ[1] ⟶ forget.obj X} (hf : IsLocallyCartesianEdge (forget.map p) f)
    (hpf : SSet.yonedaEquiv (f ≫ forget.map p) ∈ A.marked ⦋1⦌) :
    SSet.yonedaEquiv f ∈ X.marked ⦋1⦌ := by
  obtain ⟨f', hf', hy, hp'⟩ := h₂ (SimplicialObject.δ (forget.obj X : SSet.{u}) 0
    (SSet.yonedaEquiv f)) _ hpf (δ_naturality_apply (forget.map p) (0 : Fin 2) _).symm
  have hc := IsCartesianEdge.of_isLocallyCartesianEdge (forget.map p) ((h₃ f').1 hf').2
    ((yonedaEquiv_symm_comp f' _).trans ((congrArg yonedaEquiv.symm hp').trans
      (Equiv.symm_apply_apply _ _)))
    ((stdSimplex.δ_comp_yonedaEquiv_symm f' 0).trans ((congrArg yonedaEquiv.symm hy).trans
      ((stdSimplex.δ_comp_yonedaEquiv_symm _ 0).symm.trans
        (congrArg _ (Equiv.symm_apply_apply _ _))))) hf
  exact (h₃ _).2 ⟨hpf, (Equiv.symm_apply_apply SSet.yonedaEquiv f).symm ▸ hc⟩

theorem isLocallyCartesianEdge_of_simplex [InnerFibration (forget.map p)]
    (τ : Δ[2] ⟶ forget.obj X) (h₀ : IsCartesianEdge (forget.map p) (stdSimplex.δ 0 ≫ τ)) :
    (IsCartesianEdge (forget.map p) (stdSimplex.δ 2 ≫ τ) →
      IsLocallyCartesianEdge (forget.map p) (stdSimplex.δ 1 ≫ τ)) ∧
    (IsCartesianEdge (forget.map p) (stdSimplex.δ 1 ≫ τ) →
      IsLocallyCartesianEdge (forget.map p) (stdSimplex.δ 2 ≫ τ)) := by
  let τ' := pullback.lift τ (𝟙 _) (Category.id_comp (τ ≫ forget.map p)).symm
  have hk (k : Fin 3) (hk : IsCartesianEdge (forget.map p) (stdSimplex.δ k ≫ τ)) :
      IsCartesianEdge (pullback.snd (forget.map p) (τ ≫ forget.map p)) (stdSimplex.δ k ≫ τ') :=
    IsCartesianEdge.of_isPullback (IsPullback.of_hasPullback _ _)
      (by rwa [Category.assoc, pullback.lift_fst])
  have hl (k : Fin 3) (hk : IsCartesianEdge (pullback.snd (forget.map p) (τ ≫ forget.map p))
      (stdSimplex.δ k ≫ τ')) : IsLocallyCartesianEdge (forget.map p) (stdSimplex.δ k ≫ τ) := by
    have := isLocallyCartesianEdge_of_pullback (forget.map p) _ hk
    rwa [Category.assoc, pullback.lift_fst] at this
  have h := isCartesianEdge_δ_two_iff_δ_one _ τ' (hk 0 h₀)
  exact ⟨fun h₂ => hl 1 (h.1 (hk 2 h₂)), fun h₁ => hl 2 (h.2 (hk 1 h₁))⟩

private theorem hasLiftingProperty_flatSharp_of_conditions [InnerFibration (forget.map p)]
    (h₂ : ∀ (y : X.underlying _⦋0⦌) (f : A.underlying _⦋1⦌), f ∈ A.marked ⦋1⦌ →
      SimplicialObject.δ (A.underlying : SSet.{u}) 0 f = (forget.map p).app _ y →
        ∃ f' : X.underlying _⦋1⦌, f' ∈ X.marked ⦋1⦌ ∧
          SimplicialObject.δ (X.underlying : SSet.{u}) 0 f' = y ∧ (forget.map p).app _ f' = f)
    (h₃ : ∀ f : X.underlying _⦋1⦌, f ∈ X.marked ⦋1⦌ ↔
      (forget.map p).app _ f ∈ A.marked ⦋1⦌ ∧ IsCartesianEdge (forget.map p) (yonedaEquiv.symm f)) :
    HasLiftingProperty (MarkedSSet.flatSharp coherentIso.{u}) p := by
  refine (hasLiftingProperty_flatSharp_iff p _).2 fun g hg e => ?_
  let s : coherentIso.{u} ⟶ pullback (forget.map p) (g ≫ forget.map p) :=
    pullback.lift g (𝟙 _) (Category.id_comp _).symm
  have : SSet.Quasicategory (pullback (forget.map p) (g ≫ forget.map p)) :=
    quasicategory_of_innerFibration (pullback.snd _ _)
  have hc : IsCartesianEdge (pullback.snd (forget.map p) (g ≫ forget.map p))
      (yonedaEquiv.symm (s.app _ e)) :=
    isCartesianEdge_of_invStruct _
      ((Equiv.apply_symm_apply SSet.yonedaEquiv _).symm ▸ coherentIso.nonempty_invStruct_app s e)
  have hl := isLocallyCartesianEdge_of_pullback (forget.map p) _ hc
  rw [yonedaEquiv_symm_comp, ← NatTrans.comp_app_apply, pullback.lift_fst] at hl
  refine MarkedSSet.mem_marked_of_eq (Equiv.apply_symm_apply SSet.yonedaEquiv _).symm
    (mem_marked_of_isLocallyCartesianEdge p h₂ h₃ hl (MarkedSSet.mem_marked_of_eq ?_ (hg e)))
  exact (SSet.yonedaEquiv_comp _ _).trans (congrArg _ (Equiv.apply_symm_apply _ _))

private theorem hasLiftingProperty_endpointMarking_of_conditions [InnerFibration (forget.map p)]
    (h₂ : ∀ (y : X.underlying _⦋0⦌) (f : A.underlying _⦋1⦌), f ∈ A.marked ⦋1⦌ →
      SimplicialObject.δ (A.underlying : SSet.{u}) 0 f = (forget.map p).app _ y →
        ∃ f' : X.underlying _⦋1⦌, f' ∈ X.marked ⦋1⦌ ∧
          SimplicialObject.δ (X.underlying : SSet.{u}) 0 f' = y ∧ (forget.map p).app _ f' = f)
    (h₃ : ∀ f : X.underlying _⦋1⦌, f ∈ X.marked ⦋1⦌ ↔
      (forget.map p).app _ f ∈ A.marked ⦋1⦌ ∧ IsCartesianEdge (forget.map p) (yonedaEquiv.symm f)) :
    HasLiftingProperty
      (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])) □
        Arrow.mk (MarkedSSet.flatSharp Δ[1])).hom p := by
  refine ⟨fun {a b} sq => ?_⟩
  let S := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]))
    (MarkedSSet.flatSharp Δ[1])
  let σ : Δ[1] ⊗ Δ[1] ⟶ forget.obj X := forget.map (S.inl ≫ a)
  have hσ₂ : stdSimplex.δ 0 ▷ Δ[1] ≫ σ = forget.map (S.inr ≫ a) :=
    congrArg forget.map (S.isPushout.w_assoc a)
  have hσb : σ ≫ forget.map p = forget.map b :=
    (forget.map_comp _ _).symm.trans (congrArg forget.map ((Category.assoc _ _ _).trans
      ((congrArg (S.inl ≫ ·) sq.w).trans (S.inl_ι_assoc b))))
  have hcart (f : Δ[1] ⟶ forget.obj X) (hf : SSet.yonedaEquiv f ∈ X.marked ⦋1⦌) :
      IsCartesianEdge (forget.map p) f :=
    (Equiv.symm_apply_apply SSet.yonedaEquiv f) ▸ ((h₃ _).1 hf).2
  have hb (f : Δ[1] ⟶ Δ[1] ⊗ Δ[1]) :
      SSet.yonedaEquiv ((f ≫ σ) ≫ forget.map p) ∈ A.marked ⦋1⦌ :=
    MarkedSSet.mem_marked_of_eq
      (congrArg (fun φ : Δ[1] ⊗ Δ[1] ⟶ forget.obj A => φ.app _ (yonedaEquiv f))
      hσb) (MarkedPresheaf.map_mem_marked b ((MarkedSSet.mem_marked_tensor_iff _ _ _).2
        ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl,
          (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl⟩))
  have hdeg (e : (Δ[1] : SSet.{u}) _⦋1⦌) (k : Fin 2) : σ.app _
      (e, SSet.yonedaEquiv (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ k))) ∈ X.marked ⦋1⦌ :=
    MarkedPresheaf.map_mem_marked (S.inl ≫ a) ((MarkedSSet.mem_marked_tensor_iff _ _ _).2
      ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl,
        MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj Δ[1])
          (stdSimplex.obj₀Equiv.{u}.symm k)⟩)
  have hone : σ.app _ (SSet.yonedaEquiv (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)),
      SSet.yonedaEquiv (𝟙 Δ[1])) ∈ X.marked ⦋1⦌ := by
    let x : (Δ[0] ⊗ Δ[1] : SSet.{u}) _⦋1⦌ :=
      ((Δ[0] : SSet.{u}).σ 0 (SSet.yonedaEquiv (𝟙 Δ[0])), SSet.yonedaEquiv (𝟙 Δ[1]))
    have hx : ((SSet.yonedaEquiv (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)),
        SSet.yonedaEquiv (𝟙 Δ[1])) : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋1⦌) =
          (stdSimplex.δ 0 ▷ Δ[1]).app _ x :=
      Prod.ext (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl) rfl
    refine MarkedSSet.mem_marked_of_eq ((congrArg (σ.app _) hx).trans
        (congrArg (fun φ : Δ[0] ⊗ Δ[1] ⟶ forget.obj X => φ.app _ x) hσ₂))
      (MarkedPresheaf.map_mem_marked (S.inr ≫ a) (x := x)
        ((MarkedSSet.mem_marked_tensor_iff _ _ _).2
          ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl,
            (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl⟩))
  open prodStdSimplex in
  have hdiag : σ.app _ (SSet.yonedaEquiv (𝟙 Δ[1]), SSet.yonedaEquiv (𝟙 Δ[1])) ∈ X.marked ⦋1⦌ := by
    have hl (k : Fin 3) (f : Δ[1] ⟶ Δ[1] ⊗ Δ[1]) (hk : stdSimplex.δ k ≫ lowerTriangle = f) :
        stdSimplex.δ k ≫ lowerTriangle ≫ σ = f ≫ σ := by
      rw [← Category.assoc, hk]
    have h := (isLocallyCartesianEdge_of_simplex p (lowerTriangle ≫ σ)
      (hcart _ ((hl 0 _ δ_zero_lowerTriangle) ▸ hone))).1
      (hcart _ ((hl 2 _ δ_two_lowerTriangle) ▸ hdeg _ 0))
    rw [hl 1 _ δ_one_lowerTriangle] at h
    exact mem_marked_of_isLocallyCartesianEdge p h₂ h₃ h (hb _)
  open prodStdSimplex in
  have hzero : σ.app _ (SSet.yonedaEquiv (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)),
      SSet.yonedaEquiv (𝟙 Δ[1])) ∈ X.marked ⦋1⦌ := by
    have hl (k : Fin 3) (f : Δ[1] ⟶ Δ[1] ⊗ Δ[1]) (hk : stdSimplex.δ k ≫ upperTriangle = f) :
        stdSimplex.δ k ≫ upperTriangle ≫ σ = f ≫ σ := by
      rw [← Category.assoc, hk]
    have h := (isLocallyCartesianEdge_of_simplex p (upperTriangle ≫ σ)
      (hcart _ ((hl 0 _ δ_zero_upperTriangle) ▸ hdeg _ 1))).2
      (hcart _ ((hl 1 _ δ_one_upperTriangle) ▸ hdiag))
    rw [hl 2 _ δ_two_upperTriangle] at h
    exact mem_marked_of_isLocallyCartesianEdge p h₂ h₃ h (hb _)
  have hall (e : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋1⦌) : σ.app _ e ∈ X.marked ⦋1⦌ := by
    obtain ⟨e₁, e₂⟩ := e
    rcases stdSimplex.edge_one_cases e₂ with rfl | rfl | rfl
    · exact hdeg e₁ 0
    · rcases stdSimplex.edge_one_cases e₁ with rfl | rfl | rfl
      · exact hzero
      · exact hdiag
      · exact hone
    · exact hdeg e₁ 1
  exact ⟨⟨⟨edgeHomMk σ fun e _ => hall e, S.isPushout.hom_ext
    ((S.inl_ι_assoc _).trans (MarkedPresheaf.hom_ext rfl))
    ((S.inr_ι_assoc _).trans (MarkedPresheaf.hom_ext hσ₂)),
    MarkedPresheaf.hom_ext ((forget.map_comp _ _).trans hσb)⟩⟩⟩

private theorem vertex_mem_boundary {m : ℕ} (v : (Δ[m + 1] : SSet.{u}) _⦋0⦌) :
    v ∈ (∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex).obj _ := by
  refine (mem_boundary_iff_notMem_range _).2 ?_
  by_cases hv : v 0 = 0
  · exact ⟨Fin.last _, fun ⟨t, ht⟩ => Fin.last_pos.ne' (ht.symm.trans
      ((congrArg v (Subsingleton.elim (α := Fin 1) t 0)).trans hv))⟩
  · exact ⟨0, fun ⟨t, ht⟩ => hv ((congrArg v (Subsingleton.elim (α := Fin 1) 0 t)).trans ht)⟩

private theorem hasLiftingProperty_endpointBoundary_succ_of_conditions
    [InnerFibration (forget.map p)]
    (h₃ : ∀ f : X.underlying _⦋1⦌, f ∈ X.marked ⦋1⦌ ↔
      (forget.map p).app _ f ∈ A.marked ⦋1⦌ ∧ IsCartesianEdge (forget.map p) (yonedaEquiv.symm f))
    (m : ℕ) : HasLiftingProperty
      (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map
        (stdSimplex.δ 0 : Δ[0] ⟶ (Δ[1] : SSet.{u}))) □
        Arrow.mk ((MarkedPresheaf.flat edgeMarking).map
          (∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex).ι)).hom p := by
  refine ⟨fun {a b} sq => ?_⟩
  let S := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]))
    ((MarkedPresheaf.flat edgeMarking).map ∂Δ[m + 1].ι)
  let a₁ : Δ[1] ⊗ (∂Δ[m + 1] : SSet.{u}) ⟶ forget.obj X := forget.map (S.inl ≫ a)
  let a₂ : Δ[0] ⊗ Δ[m + 1] ⟶ forget.obj X := forget.map (S.inr ≫ a)
  have hw : stdSimplex.δ 0 ▷ _ ≫ a₁ = Δ[0] ◁ (∂Δ[m + 1]).ι ≫ a₂ :=
    congrArg forget.map (S.isPushout.w_assoc a)
  have hb₁ : a₁ ≫ forget.map p = Δ[1] ◁ (∂Δ[m + 1]).ι ≫ forget.map b :=
    (forget.map_comp _ _).symm.trans (congrArg forget.map ((Category.assoc _ _ _).trans
      ((congrArg (S.inl ≫ ·) sq.w).trans (S.inl_ι_assoc b))))
  have hb₂ : a₂ ≫ forget.map p = stdSimplex.δ 0 ▷ _ ≫ forget.map b :=
    (forget.map_comp _ _).symm.trans (congrArg forget.map ((Category.assoc _ _ _).trans
      ((congrArg (S.inr ≫ ·) sq.w).trans (S.inr_ι_assoc b))))
  let t := stdSimplex.isTerminalObj₀.from (Λ[1, 1] : SSet.{u})
  have hS := Subcomplex.unionProd.isPushout (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex) ∂Δ[m + 1]
  let a' := hS.desc a₁ (t ▷ _ ≫ a₂) (by
    rw [← horn_one_one_ι, comp_whiskerRight_assoc, hw, whisker_exchange_assoc])
  have hsq : CommSq a' ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd ∂Δ[m + 1]).ι
      (forget.map p) (forget.map b) := ⟨hS.hom_ext
    ((hS.inl_desc_assoc _ _ _ _).trans (hb₁.trans (Subcomplex.unionProd.ι₁_ι_assoc _ _ _).symm))
    ((hS.inr_desc_assoc _ _ _ _).trans ((Category.assoc _ _ _).trans
      ((congrArg (t ▷ _ ≫ ·) hb₂).trans ((comp_whiskerRight_assoc _ _ _ _).symm.trans
        ((congrArg (fun g : (Λ[1, 1] : SSet.{u}) ⟶ Δ[1] => g ▷ Δ[m + 1] ≫ forget.map b)
          horn_one_one_ι).trans (Subcomplex.unionProd.ι₂_ι_assoc
            (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex) ∂Δ[m + 1] (forget.map b)).symm)))))⟩
  let v₀ : (∂Δ[m + 1] : SSet.{u}) _⦋0⦌ := ⟨stdSimplex.obj₀Equiv.symm (Fin.last _), by
    rw [mem_boundary_iff_notMem_range]
    exact ⟨0, fun ⟨t, ht⟩ => (Fin.last_pos : 0 < Fin.last (m + 1)).ne' ht⟩⟩
  have hlast : prismLastEdge m ≫ a' =
      lift (𝟙 Δ[1]) (stdSimplex.σ 0 ≫ yonedaEquiv.symm v₀) ≫ a₁ := by
    have : prismLastEdge.{u} m = lift (𝟙 Δ[1]) (stdSimplex.σ 0 ≫ yonedaEquiv.symm v₀) ≫
        Subcomplex.unionProd.ι₁ _ _ :=
      (cancel_mono (Subcomplex.unionProd _ _).ι).1 (yonedaEquiv.injective rfl)
    rw [this, Category.assoc, hS.inl_desc]
  have hc : IsCartesianEdge (forget.map p) (prismLastEdge m ≫ a') := by
    rw [hlast, ← Equiv.symm_apply_apply SSet.yonedaEquiv
      (lift (𝟙 Δ[1]) (stdSimplex.σ 0 ≫ yonedaEquiv.symm v₀) ≫ a₁)]
    refine ((h₃ _).1 (MarkedPresheaf.map_mem_marked (S.inl ≫ a)
      ((MarkedSSet.mem_marked_tensor_iff _ _ _).2 ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl,
        MarkedSSet.mem_marked_of_eq ?_ (MarkedSSet.map_σ_mem_marked
          ((MarkedPresheaf.flat edgeMarking).obj (∂Δ[m + 1] : SSet.{u})) v₀)⟩))).2
    exact (congrArg SSet.yonedaEquiv (stdSimplex.σ_comp_yonedaEquiv_symm v₀ 0)).trans
      (Equiv.apply_symm_apply _ _)
  obtain ⟨l⟩ := (hc.hasLift_unionProd (forget.map p) m a' (forget.map b) hsq rfl).exists_lift
  have hl₁ : Δ[1] ◁ (∂Δ[m + 1]).ι ≫ l.l = a₁ := by
    rw [← Subcomplex.unionProd.ι₁_ι_assoc, l.fac_left, hS.inl_desc]
  have hl₂ : stdSimplex.δ 0 ▷ _ ≫ l.l = a₂ := by
    rw [← horn.ι_ι 1 0 (by decide), comp_whiskerRight_assoc, ← Subcomplex.unionProd.ι₂_ι_assoc,
      l.fac_left, hS.inr_desc, ← comp_whiskerRight_assoc,
      stdSimplex.isTerminalObj₀.hom_ext (horn.ι 1 0 (by decide) ≫ t) (𝟙 _), id_whiskerRight,
      Category.id_comp]
  have hm (e : (Δ[1] ⊗ Δ[m + 1] : SSet.{u}) _⦋1⦌)
      (he : e ∈ ((MarkedPresheaf.sharp edgeMarking).obj (Δ[1] : SSet.{u}) ⊗
        (MarkedPresheaf.flat edgeMarking).obj (Δ[m + 1] : SSet.{u})).marked ⦋1⦌) :
      l.l.app _ e ∈ X.marked ⦋1⦌ := by
    obtain ⟨-, h₂⟩ := (MarkedSSet.mem_marked_tensor_iff
      ((MarkedPresheaf.sharp edgeMarking).obj (Δ[1] : SSet.{u}))
      ((MarkedPresheaf.flat edgeMarking).obj (Δ[m + 1] : SSet.{u})) e).1 he
    obtain ⟨v, hv⟩ := exists_eq_σ_of_mem_marked_flat _ h₂
    let y : (Δ[1] ⊗ (∂Δ[m + 1] : SSet.{u}) : SSet.{u}) _⦋1⦌ :=
      (e.1, (∂Δ[m + 1] : SSet.{u}).σ 0 ⟨v, vertex_mem_boundary v⟩)
    have hy : e = (Δ[1] ◁ (∂Δ[m + 1]).ι).app _ y := Prod.ext rfl hv
    rw [hy]
    refine MarkedSSet.mem_marked_of_eq
      (congrArg (fun φ : Δ[1] ⊗ (∂Δ[m + 1] : SSet.{u}) ⟶ forget.obj X =>
      φ.app _ y) hl₁) (MarkedPresheaf.map_mem_marked (S.inl ≫ a)
        ((MarkedSSet.mem_marked_tensor_iff _ _ _).2
          ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl, MarkedSSet.map_σ_mem_marked
            ((MarkedPresheaf.flat edgeMarking).obj (∂Δ[m + 1] : SSet.{u})) _⟩))
  exact ⟨⟨⟨edgeHomMk l.l hm, S.isPushout.hom_ext
    ((S.inl_ι_assoc _).trans (MarkedPresheaf.hom_ext hl₁))
    ((S.inr_ι_assoc _).trans (MarkedPresheaf.hom_ext hl₂)),
    MarkedPresheaf.hom_ext l.fac_right⟩⟩⟩

private theorem hom_ext_tensor_stdSimplex_zero {Y Z : SSet.{u}} {g h : Y ⊗ Δ[0] ⟶ Z}
    (t : Y ⟶ Δ[0]) (hgh : lift (𝟙 Y) t ≫ g = lift (𝟙 Y) t ≫ h) : g = h := by
  have ht : fst _ _ ≫ lift (𝟙 Y) t = 𝟙 (Y ⊗ Δ[0]) :=
    CartesianMonoidalCategory.hom_ext _ _ (by simp) (stdSimplex.isTerminalObj₀.hom_ext _ _)
  rw [← Category.id_comp g, ← Category.id_comp h, ← ht, Category.assoc, Category.assoc, hgh]

private theorem hasLiftingProperty_endpointBoundary_zero_of_conditions
    (h₂ : ∀ (y : X.underlying _⦋0⦌) (f : A.underlying _⦋1⦌), f ∈ A.marked ⦋1⦌ →
      SimplicialObject.δ (A.underlying : SSet.{u}) 0 f = (forget.map p).app _ y →
        ∃ f' : X.underlying _⦋1⦌, f' ∈ X.marked ⦋1⦌ ∧
          SimplicialObject.δ (X.underlying : SSet.{u}) 0 f' = y ∧ (forget.map p).app _ f' = f) :
    HasLiftingProperty
      (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map
        (stdSimplex.δ 0 : Δ[0] ⟶ (Δ[1] : SSet.{u}))) □
        Arrow.mk ((MarkedPresheaf.flat edgeMarking).map
          (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι)).hom p := by
  refine ⟨fun {a b} sq => ?_⟩
  let S := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ (Δ[1] : SSet.{u})))
    ((MarkedPresheaf.flat edgeMarking).map (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι)
  let a₂ : Δ[0] ⊗ Δ[0] ⟶ forget.obj X := forget.map (S.inr ≫ a)
  let b₀ : Δ[1] ⊗ Δ[0] ⟶ forget.obj A := forget.map b
  have hb₂ : a₂ ≫ forget.map p = stdSimplex.δ 0 ▷ _ ≫ b₀ :=
    (forget.map_comp _ _).symm.trans (congrArg forget.map ((Category.assoc _ _ _).trans
      ((congrArg (S.inr ≫ ·) sq.w).trans (S.inr_ι_assoc b))))
  let c₀ : Δ[0] ⟶ (Δ[0] ⊗ Δ[0] : SSet.{u}) := lift (𝟙 _) (𝟙 _)
  let c₁ : Δ[1] ⟶ (Δ[1] ⊗ Δ[0] : SSet.{u}) := lift (𝟙 _) (stdSimplex.σ 0)
  have hc : stdSimplex.δ 0 ≫ c₁ = c₀ ≫ stdSimplex.δ 0 ▷ Δ[0] :=
    CartesianMonoidalCategory.hom_ext _ _ (by simp [c₀, c₁])
      (stdSimplex.isTerminalObj₀.hom_ext _ _)
  have hf : SSet.yonedaEquiv (c₁ ≫ b₀) ∈ A.marked ⦋1⦌ :=
    MarkedPresheaf.map_mem_marked b ((MarkedSSet.mem_marked_tensor_iff _ _ _).2
      ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl, MarkedSSet.mem_marked_of_eq
        (stdSimplex_zero_edge_eq _ ((Δ[0] : SSet.{u}).σ 0 (SSet.yonedaEquiv (𝟙 _))))
        (MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj Δ[0]) _)⟩)
  have hfy : SimplicialObject.δ (A.underlying : SSet.{u}) 0 (SSet.yonedaEquiv (c₁ ≫ b₀)) =
      (forget.map p).app _ (SSet.yonedaEquiv (c₀ ≫ a₂)) := by
    refine (stdSimplex.yonedaEquiv_δ_comp _ 0).symm.trans ((congrArg SSet.yonedaEquiv ?_).trans
      (SSet.yonedaEquiv_comp (c₀ ≫ a₂) (forget.map p)))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ b₀) hc).trans
      ((Category.assoc _ _ _).trans ((congrArg (c₀ ≫ ·) hb₂.symm).trans
        (Category.assoc _ _ _).symm)))
  obtain ⟨f', hf', hy, hp'⟩ := h₂ _ _ hf hfy
  refine ⟨⟨⟨edgeHomMk (fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ yonedaEquiv.symm f') fun e _ =>
    yonedaEquiv_symm_app_mem_marked hf' e.1, S.isPushout.hom_ext
      (MarkedPresheaf.hom_ext (by exact hom_ext_tensor_boundary_zero (Y := Δ[1]) _ _))
      ((S.inr_ι_assoc _).trans (MarkedPresheaf.hom_ext ?_)), MarkedPresheaf.hom_ext ?_⟩⟩⟩
  · refine hom_ext_tensor_stdSimplex_zero (𝟙 _) (Eq.trans ?_
      ((stdSimplex.δ_comp_yonedaEquiv_symm f' 0).trans ((congrArg yonedaEquiv.symm hy).trans
        (Equiv.symm_apply_apply _ _))))
    have e1 : lift (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ stdSimplex.δ 0 ▷ Δ[0] ≫
        fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) = stdSimplex.δ 0 := by
      simp
    exact congrArg (· ≫ yonedaEquiv.symm f') e1
  · refine hom_ext_tensor_stdSimplex_zero (stdSimplex.σ 0) (Eq.trans ?_
      ((yonedaEquiv_symm_comp f' _).trans ((congrArg SSet.yonedaEquiv.symm hp').trans
        (Equiv.symm_apply_apply _ _))))
    have e2 : lift (𝟙 Δ[1]) (stdSimplex.σ 0) ≫ fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) = 𝟙 _ :=
      lift_fst _ _
    exact (congrArg (fun g : Δ[1] ⟶ Δ[1] => (g ≫ yonedaEquiv.symm f') ≫ forget.map p) e2).trans
      (congrArg (· ≫ forget.map p) (Category.id_comp _))

end If

section Characterization

open SSet

theorem markedRightFibrations_iff {X A : MarkedSSet.{u}} (p : X ⟶ A) :
    markedRightFibrations p ↔
      SSet.InnerFibration (forget.map p) ∧
      (∀ (y : X.underlying _⦋0⦌) (f : A.underlying _⦋1⦌), f ∈ A.marked ⦋1⦌ →
        SimplicialObject.δ (A.underlying : SSet.{u}) 0 f = (forget.map p).app _ y →
        ∃ f' : X.underlying _⦋1⦌, f' ∈ X.marked ⦋1⦌ ∧
          SimplicialObject.δ (X.underlying : SSet.{u}) 0 f' = y ∧
          (forget.map p).app _ f' = f) ∧
      ∀ f : X.underlying _⦋1⦌, f ∈ X.marked ⦋1⦌ ↔
        (forget.map p).app _ f ∈ A.marked ⦋1⦌ ∧
          SSet.IsCartesianEdge (forget.map p) (yonedaEquiv.symm f) := by
  constructor
  · intro hp
    have := innerFibration_of_hasLiftingProperty p fun i h0 hn =>
      hp _ (markedRightGenerators.innerHorn i h0 hn)
    exact ⟨this, exists_mem_marked_of_markedRightFibrations p hp, fun f =>
      ⟨fun hf => ⟨MarkedPresheaf.map_mem_marked p hf, isCartesianEdge_of_mem_marked p hp hf⟩,
        fun ⟨h₁, h₂⟩ => mem_marked_of_isCartesianEdge p hp h₁ h₂⟩⟩
  · rintro ⟨h₁, h₂, h₃⟩ _ _ _ (⟨i, h0, hn⟩ | _ | _ | n)
    · exact ((MarkedPresheaf.flatForgetAdjunction edgeMarking).hasLiftingProperty_iff _ _).2
        (h₁.mem _ (innerHornInclusions.intro i h0 hn))
    · exact hasLiftingProperty_flatSharp_of_conditions p h₂ h₃
    · exact hasLiftingProperty_endpointMarking_of_conditions p h₂ h₃
    · cases n with
      | zero => exact hasLiftingProperty_endpointBoundary_zero_of_conditions p h₂
      | succ m => exact hasLiftingProperty_endpointBoundary_succ_of_conditions p h₃ m

theorem markedRightFibrations_llp_flatSharp (K : SSet.{u}) [K.KanComplex] :
    markedRightFibrations.llp (MarkedSSet.flatSharp K) := by
  intro X A p hp
  refine (hasLiftingProperty_flatSharp_iff p K).2 fun g hg e => ?_
  obtain ⟨G, hG⟩ := exists_coherentIso_extension (X := K) (Edge.mk' e)
    (nonempty_invStruct_of_kanComplex K e).some
  exact MarkedSSet.mem_marked_of_eq (congrArg (g.app _) hG).symm
    ((hasLiftingProperty_flatSharp_iff p coherentIso).1 (hp _ markedRightGenerators.flatSharp)
      (G ≫ g) (fun e' => hg (G.app _ e')) coherentIso.hom.edge)

theorem markedRightFibrations_iff_of_forall_mem_marked {Y A : MarkedSSet.{u}} (q : Y ⟶ A)
    (hA : ∀ e : A.underlying _⦋1⦌, e ∈ A.marked ⦋1⦌) :
    markedRightFibrations q ↔ SSet.IsCartesianFibration (forget.map q) ∧
      ∀ e : Y.underlying _⦋1⦌, e ∈ Y.marked ⦋1⦌ ↔
        SSet.IsCartesianEdge (forget.map q) (yonedaEquiv.symm e) := by
  rw [markedRightFibrations_iff]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨{ mem := h₁.mem, exists_isCartesianEdge := fun y f hf => ?_ },
      fun e => (h₃ e).trans (and_iff_right (hA _))⟩
    obtain ⟨f', hf', hy, hp⟩ := h₂ y (SSet.yonedaEquiv f) (hA _)
      ((stdSimplex.yonedaEquiv_δ_comp f 0).symm.trans ((congrArg SSet.yonedaEquiv hf).trans
        (Equiv.apply_symm_apply _ _)))
    exact ⟨yonedaEquiv.symm f', (yonedaEquiv_symm_comp f' _).trans
      ((congrArg yonedaEquiv.symm hp).trans (Equiv.symm_apply_apply _ _)),
      (stdSimplex.δ_comp_yonedaEquiv_symm f' 0).trans (congrArg yonedaEquiv.symm hy),
      ((h₃ f').1 hf').2⟩
  · rintro ⟨hc, he⟩
    refine ⟨hc.toInnerFibration, fun y f _ hfy => ?_,
      fun e => (he e).trans (and_iff_right (hA _)).symm⟩
    obtain ⟨f', h₁, h₂, h₃⟩ := hc.exists_isCartesianEdge y (yonedaEquiv.symm f)
      ((stdSimplex.δ_comp_yonedaEquiv_symm f 0).trans (congrArg yonedaEquiv.symm hfy))
    refine ⟨SSet.yonedaEquiv f', (he _).2 ((Equiv.symm_apply_apply _ f').symm ▸ h₃), ?_, ?_⟩
    · exact (stdSimplex.yonedaEquiv_δ_comp f' 0).symm.trans ((congrArg SSet.yonedaEquiv h₂).trans
        (Equiv.apply_symm_apply _ _))
    · exact (SSet.yonedaEquiv_comp f' _).symm.trans ((congrArg SSet.yonedaEquiv h₁).trans
        (Equiv.apply_symm_apply _ _))

def MarkedSSet.cartesianNatural {X S : SSet.{u}} (p : X ⟶ S) [SSet.IsCartesianFibration p] :
    MarkedSSet.{u} :=
  MarkedSSet.ofEdges X {e | SSet.IsCartesianEdge p (yonedaEquiv.symm e)} fun x => by
    have h := SSet.IsCartesianFibration.isCartesianEdge_id p (yonedaEquiv.symm x)
    rw [stdSimplex.σ_comp_yonedaEquiv_symm] at h
    exact h

noncomputable def MarkedSSet.cartesianNaturalHom {X S : SSet.{u}} (p : X ⟶ S)
    [SSet.IsCartesianFibration p] :
    MarkedSSet.cartesianNatural p ⟶ (MarkedPresheaf.sharp edgeMarking).obj S :=
  edgeHomMk p fun _ _ => (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl

theorem markedRightFibrations_cartesianNaturalHom {X S : SSet.{u}} (p : X ⟶ S)
    [SSet.IsCartesianFibration p] : markedRightFibrations (MarkedSSet.cartesianNaturalHom p) :=
  (markedRightFibrations_iff_of_forall_mem_marked _
    fun _ => (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl).2
      ⟨inferInstanceAs (SSet.IsCartesianFibration p),
        fun e => MarkedSSet.mem_marked_ofEdges _ _ _ e⟩

theorem markedRightFibrations_terminal_from_iff (X : MarkedSSet.{u}) :
    markedRightFibrations (terminal.from X) ↔ SSet.Quasicategory X.underlying ∧
      ∀ e : X.underlying _⦋1⦌, e ∈ X.marked ⦋1⦌ ↔ Nonempty (SSet.Edge.mk' e).InvStruct := by
  have hT : IsTerminal (forget.obj (⊤_ MarkedSSet.{u})) := terminalIsTerminal.isTerminalObj forget
  let i := terminalIsoIsTerminal (MarkedPresheaf.isTerminalSharpTerminal.{u} edgeMarking)
  have hTm (e : (⊤_ MarkedSSet.{u}).underlying _⦋1⦌) : e ∈ (⊤_ MarkedSSet.{u}).marked ⦋1⦌ := by
    have h : (forget.map (i.hom ≫ i.inv)).app _ e = e := by
      rw [i.hom_inv_id]
      rfl
    rw [← h]
    exact MarkedPresheaf.map_mem_marked i.inv (x := (forget.map i.hom).app _ e)
      ((MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl)
  have hP : forget.map (terminal.from X) = hT.from _ := hT.hom_ext _ _
  have hc (hq : SSet.Quasicategory X.underlying) (e : X.underlying _⦋1⦌) :
      (forget.map (terminal.from X)).app _ e ∈ (⊤_ MarkedSSet.{u}).marked ⦋1⦌ ∧
        SSet.IsCartesianEdge (forget.map (terminal.from X)) (yonedaEquiv.symm e) ↔
          Nonempty (SSet.Edge.mk' e).InvStruct := by
    rw [hP]
    refine (and_iff_right (hTm _)).trans ?_
    refine (@isCartesianEdge_iff_invStruct_of_isTerminal _ _ hq hT _).trans ?_
    exact (Equiv.apply_symm_apply SSet.yonedaEquiv e).symm ▸ Iff.rfl
  rw [markedRightFibrations_iff, ← quasicategory_iff_of_isTerminal _ hT]
  refine ⟨fun ⟨hq, _, h₃⟩ => ⟨hq, fun e => (h₃ e).trans (hc hq e)⟩,
    fun ⟨hq, h⟩ => ⟨hq, fun y f _ _ => ?_, fun e => (h e).trans (hc hq e).symm⟩⟩
  exact ⟨SimplicialObject.σ (X.underlying : SSet.{u}) 0 y, MarkedSSet.map_σ_mem_marked X y,
    δ_comp_σ_self_apply (n := 0) 0 y, yonedaEquiv.symm.injective (hT.hom_ext _ _)⟩

open MarkedSSet.modelCategoryCartesian in
theorem markedRightFibrations_terminal_from_iff_isFibrant (X : MarkedSSet.{u}) :
    markedRightFibrations (terminal.from X) ↔ IsFibrant X :=
  (markedRightFibrations_terminal_from_iff X).trans
    (MarkedSSet.modelCategoryCartesian.isFibrant_iff X).symm

end Characterization

end Atoms.Homotopical
