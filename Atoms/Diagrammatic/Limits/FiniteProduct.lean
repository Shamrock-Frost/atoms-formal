import Atoms.Diagrammatic.Limits.ConeShape

open CategoryTheory Limits Opposite Simplicial Atoms.Shape HomotopicalAlgebra

universe w u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

noncomputable def isLimitFanGrayHomRestrict {ι : Type w} (K : ι → DiagSet.{u}) [HasCoproduct K]
    (X : DiagSet.{u}) :
    IsLimit (Fan.mk ((grayHomRight (∐ K)).obj X) fun i => (grayHomRestrict (Sigma.ι K i)).app X) :=
  Fan.IsLimit.mk _
    (fun s => (grayTensorRightAdjunction (∐ K)).homEquiv _ X
      (Cofan.IsColimit.desc (isColimitOfHasCoproductOfPreservesColimit (grayTensorLeft s.pt) K)
        fun i => ((grayTensorRightAdjunction (K i)).homEquiv _ X).symm (s.proj i)))
    (fun s i => by
      refine (homEquiv_comp_grayHomRestrict (Sigma.ι K i) _).trans ?_
      exact (congrArg ((grayTensorRightAdjunction (K i)).homEquiv _ X) (Cofan.IsColimit.fac
        (isColimitOfHasCoproductOfPreservesColimit (grayTensorLeft s.pt) K) _ i)).trans
        (Equiv.apply_symm_apply _ _))
    (fun s m hm => by
      rw [← Equiv.symm_apply_eq]
      refine Cofan.IsColimit.hom_ext
        (isColimitOfHasCoproductOfPreservesColimit (grayTensorLeft s.pt) K) _ _ fun i => ?_
      refine Eq.trans ?_ (Cofan.IsColimit.fac
        (isColimitOfHasCoproductOfPreservesColimit (grayTensorLeft s.pt) K) _ i).symm
      rw [← hm i]
      exact (homEquiv_symm_comp_grayHomRestrict (Sigma.ι K i) m).symm)

section Sigma

variable {ι : Type w} {K : ι → DiagSet.{u}} [HasCoproduct K]

private theorem coneObject_sigma_hom_ext (α : Bool) (d : ∀ i, K i ⟶ X) {T : DiagSet.{u}}
    {g g' : T ⟶ coneObject α (Sigma.desc d)}
    (hπ : g ≫ coneObjectπ α (Sigma.desc d) = g' ≫ coneObjectπ α (Sigma.desc d))
    (hr : ∀ i, g ≫ coneObjectRestrict α (Sigma.ι K i) (Sigma.ι_desc d i) =
      g' ≫ coneObjectRestrict α (Sigma.ι K i) (Sigma.ι_desc d i)) : g = g' := by
  have := (grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).rightAdjoint_preservesLimits
  refine coneObject_hom_ext (Fan.IsLimit.hom_ext (isLimitFanMkObjOfIsLimit
    (grayHomRight (ball.{u} (atomSimplex 1))) _ _ (isLimitFanGrayHomRestrict K X)) _ _
      fun i => ?_) hπ
  simpa only [Category.assoc, coneObjectRestrict_ι, fan_mk_proj] using
    congrArg (· ≫ coneObjectι α (d i)) (hr i)

private theorem exists_coneObject_sigma_lift (α : Bool) (d : ∀ i, K i ⟶ X) {T : DiagSet.{u}}
    (t : T ⟶ X) (c : ∀ i, T ⟶ coneObject α (d i)) (hc : ∀ i, c i ≫ coneObjectπ α (d i) = t) :
    ∃ g : T ⟶ coneObject α (Sigma.desc d), g ≫ coneObjectπ α (Sigma.desc d) = t ∧
      ∀ i, g ≫ coneObjectRestrict α (Sigma.ι K i) (Sigma.ι_desc d i) = c i := by
  have := (grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).rightAdjoint_preservesLimits
  have := (grayTensorRightAdjunction intervalBoundary.{u}).rightAdjoint_preservesLimits
  have hI := isLimitFanMkObjOfIsLimit (grayHomRight (ball.{u} (atomSimplex 1))) _ _
    (isLimitFanGrayHomRestrict K X)
  have hB := isLimitFanMkObjOfIsLimit (grayHomRight intervalBoundary.{u}) _ _
    (isLimitFanGrayHomRestrict K X)
  set L := Fan.IsLimit.lift hI fun i => c i ≫ coneObjectι α (d i) with hL
  have hl : L ≫ (grayHomRestrict intervalBoundaryι).app _ = t ≫ coneObjectBase α (Sigma.desc d) :=
    Fan.IsLimit.hom_ext hB _ _ fun i => by
      refine ((Category.assoc _ _ _).trans ((congrArg (L ≫ ·)
        ((grayHomRestrict intervalBoundaryι).naturality _).symm).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
            (Fan.IsLimit.fac hI _ i))))).trans ?_
      rw [Category.assoc, (isPullback_coneObject α (d i)).w, ← Category.assoc, hc, Category.assoc]
      exact congrArg (t ≫ ·) (coneObjectBase_comp_grayHomRestrict α _ (Sigma.ι_desc d i)).symm
  refine ⟨(isPullback_coneObject α (Sigma.desc d)).lift L t hl,
    IsPullback.lift_snd _ _ _ _, fun i => coneObject_hom_ext ?_ ?_⟩
  · rw [Category.assoc, coneObjectRestrict_ι, ← Category.assoc, IsPullback.lift_fst]
    exact Fan.IsLimit.fac hI _ i
  · rw [Category.assoc, coneObjectRestrict_π, IsPullback.lift_snd, hc]

noncomputable def coneObjectSigmaHomEquiv (α : Bool) (d : ∀ i, K i ⟶ X) (T : DiagSet.{u}) :
    (T ⟶ coneObject α (Sigma.desc d)) ≃
      Σ t : T ⟶ X, {c : ∀ i, T ⟶ coneObject α (d i) // ∀ i, c i ≫ coneObjectπ α (d i) = t} :=
  Equiv.ofBijective
    (fun g => ⟨g ≫ coneObjectπ α (Sigma.desc d),
      fun i => g ≫ coneObjectRestrict α (Sigma.ι K i) (Sigma.ι_desc d i),
      fun i => by rw [Category.assoc, coneObjectRestrict_π]⟩)
    ⟨fun g g' hg => coneObject_sigma_hom_ext α d (congrArg Sigma.fst hg) fun i =>
        congrFun (congrArg (fun p => p.2.1) hg) i,
      fun ⟨t, c, hc⟩ => by
        obtain ⟨g, hgπ, hgc⟩ := exists_coneObject_sigma_lift α d t c hc
        exact ⟨g, Sigma.subtype_ext hgπ (funext hgc)⟩⟩

@[simp]
theorem coneObjectSigmaHomEquiv_fst (α : Bool) (d : ∀ i, K i ⟶ X) {T : DiagSet.{u}}
    (g : T ⟶ coneObject α (Sigma.desc d)) :
    (coneObjectSigmaHomEquiv α d T g).1 = g ≫ coneObjectπ α (Sigma.desc d) :=
  rfl

@[simp]
theorem coneObjectSigmaHomEquiv_snd (α : Bool) (d : ∀ i, K i ⟶ X) {T : DiagSet.{u}}
    (g : T ⟶ coneObject α (Sigma.desc d)) (i : ι) :
    (coneObjectSigmaHomEquiv α d T g).2.1 i =
      g ≫ coneObjectRestrict α (Sigma.ι K i) (Sigma.ι_desc d i) :=
  rfl

private theorem coneObjectSigmaHomEquiv_symm_π (α : Bool) (d : ∀ i, K i ⟶ X) {T : DiagSet.{u}}
    (p : Σ t : T ⟶ X, {c : ∀ i, T ⟶ coneObject α (d i) // ∀ i, c i ≫ coneObjectπ α (d i) = t}) :
    (coneObjectSigmaHomEquiv α d T).symm p ≫ coneObjectπ α (Sigma.desc d) = p.1 :=
  congrArg Sigma.fst ((coneObjectSigmaHomEquiv α d T).apply_symm_apply p)

private theorem coneObjectSigmaHomEquiv_symm_restrict (α : Bool) (d : ∀ i, K i ⟶ X)
    {T : DiagSet.{u}}
    (p : Σ t : T ⟶ X, {c : ∀ i, T ⟶ coneObject α (d i) // ∀ i, c i ≫ coneObjectπ α (d i) = t})
    (i : ι) :
    (coneObjectSigmaHomEquiv α d T).symm p ≫
      coneObjectRestrict α (Sigma.ι K i) (Sigma.ι_desc d i) = p.2.1 i :=
  congrFun (congrArg (fun q => q.2.1) ((coneObjectSigmaHomEquiv α d T).apply_symm_apply p)) i

end Sigma

section Family

variable {ι : Type w}

noncomputable abbrev familyDiagram (x : ι → X.Vertex)
    [HasCoproduct fun _ : ι => ball.{u} atomPoint] :
    (∐ fun _ : ι => ball.{u} atomPoint) ⟶ X :=
  Sigma.desc fun i => vertexHom (x i)

@[reassoc]
theorem ι_familyDiagram (x : ι → X.Vertex)
    [HasCoproduct fun _ : ι => ball.{u} atomPoint] (i : ι) :
    Sigma.ι (fun _ : ι => ball.{u} atomPoint) i ≫ familyDiagram x = vertexHom (x i) :=
  Sigma.ι_desc _ i

def IsFamilyProductCone (α : Bool) (x : ι → X.Vertex)
    [HasCoproduct fun _ : ι => ball.{u} atomPoint]
    (c : (coneObject α (familyDiagram x)).Vertex) : Prop :=
  IsLimitCone α (familyDiagram x) c

instance isIso_coneObjectπ_familyDiagram (α : Bool) [IsEmpty ι]
    (x : ι → X.Vertex) [HasCoproduct fun _ : ι => ball.{u} atomPoint] :
    IsIso (coneObjectπ α (familyDiagram x)) := by
  let s : X ⟶ coneObject α (familyDiagram x) :=
    (coneObjectSigmaHomEquiv α (fun i => vertexHom (x i)) X).symm
    ⟨𝟙 X, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  have hs : s ≫ coneObjectπ α (familyDiagram x) = 𝟙 X :=
    coneObjectSigmaHomEquiv_symm_π α _ _
  refine ⟨s, coneObject_sigma_hom_ext α _ ?_ fun i => isEmptyElim i, hs⟩
  exact (Category.assoc _ _ _).trans ((congrArg (coneObjectπ α (familyDiagram x) ≫ ·) hs).trans
    ((Category.comp_id _).trans (Category.id_comp _).symm))

theorem isFamilyProductCone_empty_iff (α : Bool) [IsEmpty ι] (hX : IsInftyCategory 1 X)
    (x : ι → X.Vertex) [HasCoproduct fun _ : ι => ball.{u} atomPoint]
    (c : (coneObject α (familyDiagram x)).Vertex) :
    IsFamilyProductCone α x c ↔
      X.HasContractibleHoms α (DiagSet.Vertex.map (coneObjectπ α (familyDiagram x)) c) :=
  have : WeakEquivalence ((DiagSet.toInfty 1).map (coneObjectπ α (familyDiagram x))) :=
    (weakEquivalence_iff _).2 ((weakEquivalences _).of_isIso _)
  (DiagSet.hasContractibleHoms_map_iff (isInftyCategory_coneObject α _ hX) hX _ α c).symm

theorem sigmaWhiskerEquiv_familyDiagram {ι' : Type w} (e : ι' ≃ ι)
    (x : ι → X.Vertex) [HasCoproduct fun _ : ι => ball.{u} atomPoint]
    [HasCoproduct fun _ : ι' => ball.{u} atomPoint] :
    (Sigma.whiskerEquiv (f := fun _ : ι' => ball.{u} atomPoint)
        (g := fun _ : ι => ball.{u} atomPoint) e fun _ => Iso.refl _).hom ≫
      familyDiagram x = familyDiagram (x ∘ e) :=
  Sigma.hom_ext _ _ fun j => by
    rw [Sigma.whiskerEquiv_hom, Sigma.ι_comp_map'_assoc, Iso.refl_inv, Category.id_comp,
      ι_familyDiagram, ι_familyDiagram]
    rfl

theorem isFamilyProductCone_equiv_iff {ι' : Type w} (α : Bool) (e : ι' ≃ ι)
    (x : ι → X.Vertex) [HasCoproduct fun _ : ι => ball.{u} atomPoint]
    [HasCoproduct fun _ : ι' => ball.{u} atomPoint]
    (c : (coneObject α (familyDiagram x)).Vertex) :
    IsFamilyProductCone α (x ∘ e) (DiagSet.Vertex.map (coneObjectRestrict α _
      (sigmaWhiskerEquiv_familyDiagram e x)) c) ↔ IsFamilyProductCone α x c :=
  isLimitCone_coneObjectRestrict_iff_of_isIso α _ _ c

theorem isFamilyProductCone_unique_iff (α : Bool) [Unique ι]
    (x : ι → X.Vertex) [HasCoproduct fun _ : ι => ball.{u} atomPoint]
    (c : (coneObject α (familyDiagram x)).Vertex) :
    IsLimitCone α (vertexHom (x default)) (DiagSet.Vertex.map (coneObjectRestrict α _
      (ι_familyDiagram x default)) c) ↔ IsFamilyProductCone α x c :=
  have : IsIso (Sigma.ι (fun _ : ι => ball.{u} atomPoint) default) :=
    inferInstanceAs (IsIso (coproductUniqueIso _).inv)
  isLimitCone_coneObjectRestrict_iff_of_isIso α _ _ c

end Family

theorem sigmaMap'_familyDiagram {n : ℕ} (x : Fin (n + 1) → X.Vertex) :
    Sigma.map' (f := fun _ : Fin n => ball.{u} atomPoint)
        (g := fun _ : Fin (n + 1) => ball.{u} atomPoint) Fin.castSucc (fun _ => 𝟙 _) ≫
      familyDiagram x = familyDiagram (x ∘ Fin.castSucc) :=
  Sigma.hom_ext _ _ fun j => by
    rw [Sigma.ι_comp_map'_assoc, Category.id_comp, ι_familyDiagram, ι_familyDiagram]
    rfl

private theorem coneObjectRestrict_sigmaMap'_ι {n : ℕ} (α : Bool)
    (x : Fin (n + 1) → X.Vertex) (j : Fin n) :
    coneObjectRestrict α _ (sigmaMap'_familyDiagram x) ≫
        coneObjectRestrict α _ (ι_familyDiagram (x ∘ Fin.castSucc) j) =
      coneObjectRestrict α _ (ι_familyDiagram x (Fin.castSucc j)) := by
  rw [coneObjectRestrict_comp]
  exact coneObjectRestrict_congr α ((Sigma.ι_comp_map' _ _ _).trans (Category.id_comp _)) _ _

theorem isPullback_coneObject_familyDiagram_succ (α : Bool) {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) :
    IsPullback (coneObjectRestrict α _ (sigmaMap'_familyDiagram x))
      (coneObjectRestrict α _ (ι_familyDiagram x (Fin.last n)))
      (coneObjectπ α (familyDiagram (x ∘ Fin.castSucc)))
      (coneObjectπ α (vertexHom (x (Fin.last n)))) := by
  have w : coneObjectRestrict α _ (sigmaMap'_familyDiagram x) ≫
      coneObjectπ α (familyDiagram (x ∘ Fin.castSucc)) =
      coneObjectRestrict α _ (ι_familyDiagram x (Fin.last n)) ≫
          coneObjectπ α (vertexHom (x (Fin.last n))) := by
    rw [coneObjectRestrict_π, coneObjectRestrict_π]
  let c (s : PullbackCone (coneObjectπ α (familyDiagram (x ∘ Fin.castSucc)))
      (coneObjectπ α (vertexHom (x (Fin.last n))))) (i : Fin (n + 1)) :
      s.pt ⟶ coneObject α (vertexHom (x i)) :=
    Fin.lastCases (motive := fun i => s.pt ⟶ coneObject α (vertexHom (x i))) s.snd
      (fun j => s.fst ≫ coneObjectRestrict α _ (ι_familyDiagram (x ∘ Fin.castSucc) j)) i
  have hc_last (s : PullbackCone (coneObjectπ α (familyDiagram (x ∘ Fin.castSucc)))
      (coneObjectπ α (vertexHom (x (Fin.last n))))) : c s (Fin.last n) = s.snd :=
    Fin.lastCases_last (motive := fun i => s.pt ⟶ coneObject α (vertexHom (x i)))
  have hc_cast (s : PullbackCone (coneObjectπ α (familyDiagram (x ∘ Fin.castSucc)))
      (coneObjectπ α (vertexHom (x (Fin.last n))))) (j : Fin n) :
      c s (Fin.castSucc j) =
        s.fst ≫ coneObjectRestrict α _ (ι_familyDiagram (x ∘ Fin.castSucc) j) :=
    Fin.lastCases_castSucc (motive := fun i => s.pt ⟶ coneObject α (vertexHom (x i))) j
  have hc (s : PullbackCone (coneObjectπ α (familyDiagram (x ∘ Fin.castSucc)))
      (coneObjectπ α (vertexHom (x (Fin.last n))))) (i : Fin (n + 1)) :
      c s i ≫ coneObjectπ α (vertexHom (x i)) =
        s.fst ≫ coneObjectπ α (familyDiagram (x ∘ Fin.castSucc)) := by
    induction i using Fin.lastCases with
    | last =>
      exact (congrArg (· ≫ coneObjectπ α (vertexHom (x (Fin.last n)))) (hc_last s)).trans
        s.condition.symm
    | cast j =>
      exact (congrArg (· ≫ coneObjectπ α (vertexHom (x (Fin.castSucc j)))) (hc_cast s j)).trans
        ((Category.assoc _ _ _).trans (congrArg (s.fst ≫ ·) (coneObjectRestrict_π α _ _)))
  let l (s : PullbackCone (coneObjectπ α (familyDiagram (x ∘ Fin.castSucc)))
      (coneObjectπ α (vertexHom (x (Fin.last n))))) :
      s.pt ⟶ coneObject α (familyDiagram x) :=
    (coneObjectSigmaHomEquiv α (fun i => vertexHom (x i)) s.pt).symm ⟨_, c s, hc s⟩
  have hl (s : PullbackCone (coneObjectπ α (familyDiagram (x ∘ Fin.castSucc)))
      (coneObjectπ α (vertexHom (x (Fin.last n))))) (i : Fin (n + 1)) :
      l s ≫ coneObjectRestrict α _ (ι_familyDiagram x i) = c s i :=
    coneObjectSigmaHomEquiv_symm_restrict (K := fun _ : Fin (n + 1) => ball.{u} atomPoint)
      α (fun i => vertexHom (x i)) ⟨_, c s, hc s⟩ i
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w l (fun s => ?_) (fun s => ?_)
    (fun s m hm₁ hm₂ => ?_))
  · refine coneObject_sigma_hom_ext α (fun j => vertexHom (x (Fin.castSucc j))) ?_ fun j => ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (l s ≫ ·) (coneObjectRestrict_π α _ _)).trans
        (coneObjectSigmaHomEquiv_symm_π (K := fun _ : Fin (n + 1) => ball.{u} atomPoint)
          α (fun i => vertexHom (x i)) ⟨_, c s, hc s⟩))
    · rw [Category.assoc]
      refine (congrArg (l s ≫ ·) (coneObjectRestrict_sigmaMap'_ι α x j)).trans ?_
      exact (hl s _).trans (hc_cast s j)
  · exact (hl s _).trans (hc_last s)
  · refine coneObject_sigma_hom_ext α (fun i => vertexHom (x i)) ?_ fun i => ?_
    · exact (congrArg (m ≫ ·)
        (coneObjectRestrict_π α _ (ι_familyDiagram x (Fin.last n))).symm).trans
        (((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ coneObjectπ α (vertexHom (x (Fin.last n)))) hm₂)).trans
          (s.condition.symm.trans (coneObjectSigmaHomEquiv_symm_π
            (K := fun _ : Fin (n + 1) => ball.{u} atomPoint)
            α (fun i => vertexHom (x i)) ⟨_, c s, hc s⟩).symm))
    · refine Eq.trans ?_ (hl s i).symm
      induction i using Fin.lastCases with
      | last => exact hm₂.trans (hc_last s).symm
      | cast j =>
        exact (congrArg (m ≫ ·) (coneObjectRestrict_sigmaMap'_ι α x j)).symm.trans
          (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hm₁)).trans (hc_cast s j).symm)

noncomputable def sigmaFinTwoIso :
    (∐ fun _ : Fin 2 => ball.{u} atomPoint) ≅ intervalBoundary.{u} where
  hom := Sigma.desc fun i => Fin.cases coprod.inl (fun _ => coprod.inr) i
  inv := coprod.desc (Sigma.ι (fun _ : Fin 2 => ball.{u} atomPoint) 0)
    (Sigma.ι (fun _ : Fin 2 => ball.{u} atomPoint) 1)
  hom_inv_id := Sigma.hom_ext _ _ fun i => by
    fin_cases i
    · exact (Sigma.ι_desc_assoc _ _ _).trans ((coprod.inl_desc _ _).trans (Category.comp_id _).symm)
    · exact (Sigma.ι_desc_assoc _ _ _).trans ((coprod.inr_desc _ _).trans (Category.comp_id _).symm)
  inv_hom_id := coprod.hom_ext
    ((coprod.inl_desc_assoc _ _ _).trans ((Sigma.ι_desc _ _).trans (Category.comp_id _).symm))
    ((coprod.inr_desc_assoc _ _ _).trans ((Sigma.ι_desc _ _).trans (Category.comp_id _).symm))

theorem sigmaFinTwoIso_hom_pairDiagram (x y : X.Vertex) :
    sigmaFinTwoIso.hom ≫ pairDiagram x y = familyDiagram ![x, y] :=
  Sigma.hom_ext _ _ fun i => by
    fin_cases i
    · exact (Sigma.ι_desc_assoc _ _ _).trans ((coprod.inl_desc _ _).trans
        (ι_familyDiagram ![x, y] 0).symm)
    · exact (Sigma.ι_desc_assoc _ _ _).trans ((coprod.inr_desc _ _).trans
        (ι_familyDiagram ![x, y] 1).symm)

theorem isFamilyProductCone_finTwo_iff (α : Bool) (x y : X.Vertex)
    (c : (coneObject α (pairDiagram x y)).Vertex) :
    IsFamilyProductCone α ![x, y] (DiagSet.Vertex.map (coneObjectRestrict α sigmaFinTwoIso.hom
      (sigmaFinTwoIso_hom_pairDiagram x y)) c) ↔ IsProductCone α x y c :=
  isLimitCone_coneObjectRestrict_iff_of_isIso α _ _ c

end Atoms.Diagrammatic
