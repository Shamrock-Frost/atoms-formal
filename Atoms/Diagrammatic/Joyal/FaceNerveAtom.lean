import Atoms.Diagrammatic.Joyal.FaceNerveHomotopy
import Atoms.Molecule.Vertex

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Diagrammatic

open MarkedSSet.modelCategoryCartesian

section MarkedSubcomplex

variable {X : SSet.{u}} (M : Set (X _⦋1⦌))

noncomputable abbrev markedSubcomplex (A : X.Subcomplex) : MarkedSSet :=
  (overMarking X M).obj (Over.mk A.ι)

noncomputable def markedSubcomplexMap {A B : X.Subcomplex} (h : A ≤ B) :
    markedSubcomplex M A ⟶ markedSubcomplex M B :=
  (overMarking X M).map (Over.homMk (SSet.Subcomplex.homOfLE h))

theorem forget_map_markedSubcomplexMap {A B : X.Subcomplex} (h : A ≤ B) :
    MarkedPresheaf.forget.map (markedSubcomplexMap M h) = SSet.Subcomplex.homOfLE h :=
  rfl

instance mono_markedSubcomplexMap {A B : X.Subcomplex} (h : A ≤ B) :
    Mono (markedSubcomplexMap M h) :=
  (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (SSet.Subcomplex.homOfLE h)))

theorem markedSubcomplexMap_comp {A B D : X.Subcomplex} (h₁ : A ≤ B) (h₂ : B ≤ D) :
    markedSubcomplexMap M h₁ ≫ markedSubcomplexMap M h₂ =
      markedSubcomplexMap M (h₁.trans h₂) :=
  MarkedPresheaf.hom_ext rfl

theorem weakEquivalence_markedSubcomplexMap_of_eq {A B : X.Subcomplex} (h : A = B) :
    WeakEquivalence (markedSubcomplexMap M h.le) := by
  subst h
  have e : markedSubcomplexMap M (le_refl A) = 𝟙 _ := MarkedPresheaf.hom_ext rfl
  rw [e]
  infer_instance

private theorem trivialCofibrations_markedSubcomplexMap {A B : X.Subcomplex} (h : A ≤ B)
    [WeakEquivalence (markedSubcomplexMap M h)] :
    trivialCofibrations MarkedSSet (markedSubcomplexMap M h) :=
  (mem_trivialCofibrations_iff _).2
    ⟨(cofibration_iff _).2 (inferInstance : Mono (markedSubcomplexMap M h)), inferInstance⟩

theorem weakEquivalence_markedSubcomplexMap_of_bicartSq {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : A₁.BicartSq A₂ A₃ A₄) [WeakEquivalence (markedSubcomplexMap M sq.le₁₃)] :
    WeakEquivalence (markedSubcomplexMap M sq.le₂₄) := by
  have hp := isPushout_overMarking_map (M := M)
    (f₁ := (Over.homMk (SSet.Subcomplex.homOfLE sq.le₁₂) : Over.mk A₁.ι ⟶ Over.mk A₂.ι))
    (f₂ := (Over.homMk (SSet.Subcomplex.homOfLE sq.le₁₃) : Over.mk A₁.ι ⟶ Over.mk A₃.ι))
    (g₁ := (Over.homMk (SSet.Subcomplex.homOfLE sq.le₂₄) : Over.mk A₂.ι ⟶ Over.mk A₄.ι))
    (g₂ := (Over.homMk (SSet.Subcomplex.homOfLE sq.le₃₄) : Over.mk A₃.ι ⟶ Over.mk A₄.ι))
    sq.isPushout
  exact ((mem_trivialCofibrations_iff _).1 (MorphismProperty.of_isPushout hp
    (trivialCofibrations_markedSubcomplexMap M sq.le₁₃))).2

noncomputable def markedSubcomplexRemark {M M' : Set (X _⦋1⦌)} (h : M ⊆ M') (A : X.Subcomplex) :
    markedSubcomplex M A ⟶ markedSubcomplex M' A :=
  MarkedSSet.ofEdgeSetHom (𝟙 _) _ _ fun _ he => h he

theorem markedSubcomplexMap_comp_markedSubcomplexRemark {M M' : Set (X _⦋1⦌)} (hM : M ⊆ M')
    {A B : X.Subcomplex} (h : A ≤ B) :
    markedSubcomplexMap M h ≫ markedSubcomplexRemark hM B =
      markedSubcomplexRemark hM A ≫ markedSubcomplexMap M' h :=
  MarkedPresheaf.hom_ext rfl

variable {M} in
private theorem isPushout_markedSubcomplexRemark {M' : Set (X _⦋1⦌)} (hM : M ⊆ M')
    {A B : X.Subcomplex} (h : A ≤ B)
    (hB : ∀ e : B.toSSet _⦋1⦌, e.1 ∈ M' → e.1 ∈ M ∨ e.1 ∈ A.obj _) :
    IsPushout (markedSubcomplexMap M h) (markedSubcomplexRemark hM A)
      (markedSubcomplexRemark hM B) (markedSubcomplexMap M' h) := by
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _
      (markedSubcomplexMap_comp_markedSubcomplexRemark hM h))
    (MarkedPresheaf.isColimitOfForget _ ?_ fun ⟨n⟩ y hy ↦ ?_)
  · exact (isColimitMapCoconePushoutCoconeEquiv MarkedPresheaf.forget _).symm
      (IsPushout.id_vert (SSet.Subcomplex.homOfLE h)).isColimit
  · obtain rfl : n = 1 := MarkedSSet.len_eq_one_of_mem_marked _ hy
    rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ y).1 hy with hy | ⟨v, rfl⟩
    · rcases hB y hy with hy' | hy'
      · exact ⟨WalkingSpan.left, y, (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl hy'), rfl⟩
      · exact ⟨WalkingSpan.right, ⟨y.1, hy'⟩,
          (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl hy), rfl⟩
    · exact ⟨WalkingSpan.left, B.toSSet.σ 0 v,
        (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inr ⟨v, rfl⟩), rfl⟩

variable {M} in
theorem weakEquivalence_markedSubcomplexMap_of_subset {M' : Set (X _⦋1⦌)} (hM : M ⊆ M')
    {A B : X.Subcomplex} (h : A ≤ B)
    (hB : ∀ e : B.toSSet _⦋1⦌, e.1 ∈ M' → e.1 ∈ M ∨ e.1 ∈ A.obj _)
    [WeakEquivalence (markedSubcomplexMap M h)] :
    WeakEquivalence (markedSubcomplexMap M' h) :=
  ((mem_trivialCofibrations_iff _).1 (MorphismProperty.of_isPushout
    (isPushout_markedSubcomplexRemark hM h hB).flip
    (trivialCofibrations_markedSubcomplexMap M h))).2

section InnerAnodyne

theorem weakEquivalence_markedSubcomplexMap_of_innerAnodyneExtensions {A B : X.Subcomplex}
    (h : A ≤ B) (hi : SSet.innerAnodyneExtensions (SSet.Subcomplex.homOfLE h))
    (hM : ∀ e : B.toSSet _⦋1⦌, e.1 ∈ M → e.1 ∈ A.obj _) :
    WeakEquivalence (markedSubcomplexMap M h) := by
  have hf : WeakEquivalence ((MarkedPresheaf.flat edgeMarking).map (SSet.Subcomplex.homOfLE h)) :=
    (weakEquivalence_flat_map_iff _).2
      (SSet.modelCategoryJoyal.weakEquivalence_of_innerAnodyneExtensions _ hi)
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
  have h₀ : cartesianCylinder.{u}.trivialCofibrations cartesianGenerators
      (MarkedSSet.ofEdgeSetHom (SSet.Subcomplex.homOfLE h) ∅ ∅ fun _ h ↦ h.elim) :=
    ((cartesianCylinder.{u}.trivialCofibrations cartesianGenerators).arrow_mk_iso_iff
      (Arrow.isoMk (e _) (e _) (MarkedPresheaf.hom_ext rfl))).1
      ⟨(MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (SSet.Subcomplex.homOfLE h))),
        (weakEquivalence_iff _).1 hf⟩
  exact (weakEquivalence_iff _).2 (trivialCofibrations_ofEdgeSetHom_of_subset
    (SSet.Subcomplex.homOfLE h) (E₁ := {e | A.ι.app _ e ∈ M}) (F₁ := {e | B.ι.app _ e ∈ M})
    (Set.empty_subset _) (fun _ h ↦ h.elim) (fun _ h ↦ h) (Set.empty_subset _)
    (fun e he ↦ ⟨⟨e.1, hM e he⟩, he, rfl⟩) h₀).2

end InnerAnodyne

end MarkedSubcomplex

section Chains

variable {C : Type} [PartialOrder C]

def chainSubcomplex (T : Set C) : (nerve (ULift.{u} C)).Subcomplex where
  obj _ := {σ | ∀ i, (σ.obj i).down ∈ T}
  map _ _ hσ _ := hσ _

theorem mem_chainSubcomplex {T : Set C} {n : SimplexCategoryᵒᵖ} (σ : (nerve (ULift.{u} C)).obj n) :
    σ ∈ (chainSubcomplex.{u} T).obj n ↔ ∀ i, (σ.obj i).down ∈ T :=
  Iff.rfl

theorem chainSubcomplex_mono {T T' : Set C} (h : T ⊆ T') :
    chainSubcomplex.{u} T ≤ chainSubcomplex T' :=
  fun _ _ hσ i => h (hσ i)

theorem chainSubcomplex_inter (T T' : Set C) :
    chainSubcomplex.{u} (T ∩ T') = chainSubcomplex T ⊓ chainSubcomplex T' := by
  ext n σ
  exact forall_and

private theorem sup_inf_right' {X : SSet.{u}} (A B D : X.Subcomplex) :
    (A ⊔ B) ⊓ D = A ⊓ D ⊔ B ⊓ D := by
  ext n σ
  simp only [Subfunctor.min_obj, Subfunctor.max_obj, Set.mem_inter_iff, Set.mem_union]
  tauto

theorem chainSubcomplex_sup_inf (T₁ T₂ T₃ : Set C) :
    (chainSubcomplex.{u} T₁ ⊔ chainSubcomplex T₂) ⊓ chainSubcomplex T₃ =
      chainSubcomplex (T₁ ∩ T₃) ⊔ chainSubcomplex (T₂ ∩ T₃) := by
  ext n σ
  simp only [Subfunctor.min_obj, Subfunctor.max_obj, Set.mem_inter_iff, Set.mem_union,
    mem_chainSubcomplex, forall_and]
  tauto

theorem chainSubcomplex_union {T T' : Set C}
    (h : ∀ a ∈ T, ∀ b ∈ T', a ≤ b ∨ b ≤ a → a ∈ T' ∨ b ∈ T) :
    chainSubcomplex.{u} (T ∪ T') = chainSubcomplex T ⊔ chainSubcomplex T' := by
  refine le_antisymm (fun n σ hσ => ?_) (sup_le (chainSubcomplex_mono Set.subset_union_left)
    (chainSubcomplex_mono Set.subset_union_right))
  by_contra hn
  simp only [Subfunctor.max_obj, Set.mem_union, mem_chainSubcomplex, not_or, not_forall] at hn
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hn
  have hiT' : (σ.obj i).down ∈ T' := (hσ i).resolve_left hi
  have hjT : (σ.obj j).down ∈ T := (hσ j).resolve_right hj
  have hc : (σ.obj j).down ≤ (σ.obj i).down ∨ (σ.obj i).down ≤ (σ.obj j).down := by
    rcases le_total i j with hij | hij
    · exact Or.inr (ULift.down_le.2 (leOfHom (σ.map (homOfLE hij))))
    · exact Or.inl (ULift.down_le.2 (leOfHom (σ.map (homOfLE hij))))
  rcases h _ hjT _ hiT' hc with h' | h'
  · exact hj h'
  · exact hi h'

def chainMap {D : Type} [PartialOrder D] {T : Set C} {T' : Set D} (f : C → D)
    (hf : ∀ a ∈ T, ∀ b ∈ T, a ≤ b → f a ≤ f b) (hfT : ∀ a ∈ T, f a ∈ T') :
    (chainSubcomplex.{u} T).toSSet ⟶ (chainSubcomplex T').toSSet where
  app _ := ↾fun σ => ⟨Monotone.functor (f := fun i => ULift.up (f (σ.1.obj i).down))
    (fun i j h => hf _ (σ.2 i) _ (σ.2 j) (ULift.down_le.2 (leOfHom (σ.1.map (homOfLE h))))),
    fun i => hfT _ (σ.2 i)⟩
  naturality _ _ _ := by
    ext σ
    exact Subtype.ext (nerve.ext_of_isThin rfl)

def edgeSet (R : C → C → Prop) : Set ((nerve (ULift.{u} C)) _⦋1⦌) :=
  {e | R (e.obj 0).down (e.obj 1).down}

theorem edgeSet_mono {R R' : C → C → Prop} (h : ∀ a b, R a b → R' a b) :
    edgeSet.{u} R ⊆ edgeSet R' :=
  fun _ he => h _ _ he

theorem obj_zero_le_obj_one (e : (nerve (ULift.{u} C)) _⦋1⦌) : (e.obj 0).down ≤ (e.obj 1).down :=
  ULift.down_le.2 (leOfHom (e.map (homOfLE (Fin.zero_le 1))))

private theorem exists_σ_eq_of_obj_eq {A : (nerve (ULift.{u} C)).Subcomplex} (e : A.toSSet _⦋1⦌)
    (h : e.1.obj 0 = e.1.obj 1) : ∃ x, A.toSSet.σ 0 x = e := by
  refine ⟨A.toSSet.δ 1 e, Subtype.ext (nerve.ext_of_isThin (funext fun i => ?_))⟩
  fin_cases i
  · rfl
  · exact h

theorem mem_marked_markedSubcomplex_iff (R : C → C → Prop)
    {A : (nerve (ULift.{u} C)).Subcomplex} (e : A.toSSet _⦋1⦌) :
    e ∈ (markedSubcomplex (edgeSet.{u} R) A).marked ⦋1⦌ ↔
      R (e.1.obj 0).down (e.1.obj 1).down ∨ (e.1.obj 0).down = (e.1.obj 1).down := by
  refine (MarkedSSet.mem_marked_ofEdgeSet _ _ _).trans ⟨?_, ?_⟩
  · rintro (h | ⟨x, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (congrArg (fun i => (x.1.obj i).down) (Subsingleton.elim (α := Fin 1) _ _))
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (exists_σ_eq_of_obj_eq e (ULift.ext _ _ h))

private theorem edge_ext {A : (nerve (ULift.{u} C)).Subcomplex} {e e' : A.toSSet _⦋1⦌}
    (h₀ : e.1.obj 0 = e'.1.obj 0) (h₁ : e.1.obj 1 = e'.1.obj 1) : e = e' := by
  refine Subtype.ext (nerve.ext_of_isThin (funext fun i => ?_))
  fin_cases i
  · exact h₀
  · exact h₁

private def chainTriangle {T : Set C} {a b c : C} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T)
    (hab : a ≤ b) (hbc : b ≤ c) : (chainSubcomplex.{u} T).toSSet _⦋2⦌ :=
  ⟨ComposableArrows.mk₂ (homOfLE (ULift.up_le.2 hab)) (homOfLE (ULift.up_le.2 hbc)), fun i => by
    fin_cases i
    · exact ha
    · exact hb
    · exact hc⟩

theorem weakEquivalence_markedSubcomplexRemark_chainSubcomplex {R R' : C → C → Prop}
    (hRR' : ∀ a b, R a b → R' a b) (T : Set C)
    (h : ∀ a ∈ T, ∀ b ∈ T, a ≤ b → R' a b → R a b ∨ ∃ c ∈ T,
      (c ≤ a ∧ (R c a ∨ c = a) ∧ (R c b ∨ c = b)) ∨
      (a ≤ c ∧ c ≤ b ∧ (R a c ∨ a = c) ∧ (R c b ∨ c = b)) ∨
      (b ≤ c ∧ (R a c ∨ a = c) ∧ (R b c ∨ b = c))) :
    WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hRR') (chainSubcomplex.{u} T)) := by
  refine weakEquivalence_ofEdgeSetHom_id (Z := (chainSubcomplex T).toSSet)
    (fun _ he => edgeSet_mono hRR' he) fun F _ g hg e he => ?_
  have hm (e' : (chainSubcomplex.{u} T).toSSet _⦋1⦌)
      (he' : R (e'.1.obj 0).down (e'.1.obj 1).down ∨ (e'.1.obj 0).down = (e'.1.obj 1).down) :
      Nonempty (SSet.Edge.mk' (g.app _ e')).InvStruct := by
    rcases he' with he' | he'
    · exact hg e' he'
    · obtain ⟨x, rfl⟩ := exists_σ_eq_of_obj_eq e' (ULift.ext _ _ he')
      rw [SSet.σ_naturality_apply]
      exact SSet.nonempty_invStruct_σ _
  have ha : (e.1.obj 0).down ∈ T := e.2 0
  have hb : (e.1.obj 1).down ∈ T := e.2 1
  rcases h _ ha _ hb (obj_zero_le_obj_one e.1) he with hR | ⟨c, hc, h₁ | h₁ | h₁⟩
  · exact hg e hR
  · obtain ⟨hca, hR₁, hR₂⟩ := h₁
    let σ := chainTriangle hc ha hb hca (obj_zero_le_obj_one e.1)
    rw [edge_ext (e := e) (e' := (chainSubcomplex T).toSSet.δ 0 σ) rfl rfl]
    exact SSet.nonempty_invStruct_congr (SSet.δ_naturality_apply g 0 σ).symm
      (SSet.nonempty_invStruct_δ_zero (g.app _ σ)
        (SSet.nonempty_invStruct_congr (SSet.δ_naturality_apply g 2 σ) (hm _ hR₁))
        (SSet.nonempty_invStruct_congr (SSet.δ_naturality_apply g 1 σ) (hm _ hR₂)))
  · obtain ⟨hac, hcb, hR₁, hR₂⟩ := h₁
    let σ := chainTriangle ha hc hb hac hcb
    rw [edge_ext (e := e) (e' := (chainSubcomplex T).toSSet.δ 1 σ) rfl rfl]
    exact SSet.nonempty_invStruct_congr (SSet.δ_naturality_apply g 1 σ).symm
      (SSet.nonempty_invStruct_δ_one (g.app _ σ)
        (SSet.nonempty_invStruct_congr (SSet.δ_naturality_apply g 2 σ) (hm _ hR₁))
        (SSet.nonempty_invStruct_congr (SSet.δ_naturality_apply g 0 σ) (hm _ hR₂)))
  · obtain ⟨hbc, hR₁, hR₂⟩ := h₁
    let σ := chainTriangle ha hb hc (obj_zero_le_obj_one e.1) hbc
    rw [edge_ext (e := e) (e' := (chainSubcomplex T).toSSet.δ 2 σ) rfl rfl]
    exact SSet.nonempty_invStruct_congr (SSet.δ_naturality_apply g 2 σ).symm
      (SSet.nonempty_invStruct_δ_two (g.app _ σ)
        (SSet.nonempty_invStruct_congr (SSet.δ_naturality_apply g 0 σ) (hm _ hR₂))
        (SSet.nonempty_invStruct_congr (SSet.δ_naturality_apply g 1 σ) (hm _ hR₁)))

section Retraction

open MonoidalCategory

variable (R : C → C → Prop) {T T' : Set C} (r : C → C) (ε : Bool)

private def retractionHomotopy (s : ULift.{u} (Fin 2)) (a : C) : C :=
  if s.down = 0 then cond ε (r a) a else cond ε a (r a)

variable {r ε} in
private theorem retractionHomotopy_mono (hr : ∀ a ∈ T', ∀ b ∈ T', a ≤ b → r a ≤ r b)
    (hle : ∀ a ∈ T', cond ε (r a ≤ a) (a ≤ r a)) {s s' : ULift.{u} (Fin 2)} {a b : C}
    (hs : s ≤ s') (ha : a ∈ T') (hb : b ∈ T') (hab : a ≤ b) :
    retractionHomotopy r ε s a ≤ retractionHomotopy r ε s' b := by
  obtain ⟨s⟩ := s
  obtain ⟨s'⟩ := s'
  have hs' : s ≤ s' := hs
  rw [retractionHomotopy, retractionHomotopy]
  fin_cases s <;> fin_cases s' <;> cases ε
  all_goals simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero, cond_false,
    cond_true]
  all_goals first
    | exact hab
    | exact hr a ha b hb hab
    | exact hab.trans (hle b hb)
    | exact (hle a ha).trans hab
    | exact absurd hs' (by decide)

omit [PartialOrder C] in
variable {r ε} in
private theorem retractionHomotopy_mem (hrT : ∀ a ∈ T', r a ∈ T) (hT : T ⊆ T')
    (s : ULift.{u} (Fin 2)) {a : C} (ha : a ∈ T') : retractionHomotopy r ε s a ∈ T' := by
  rw [retractionHomotopy]
  split_ifs <;> cases ε
  all_goals first | exact ha | exact hT (hrT _ ha)

variable {R r ε} in
private theorem retractionHomotopy_rel
    (hR : ∀ a ∈ T', ∀ b ∈ T', a ≤ b → (R a b ∨ a = b) →
      (R (r a) (r b) ∨ r a = r b) ∧ cond ε (R (r a) b ∨ r a = b) (R a (r b) ∨ a = r b))
    {s s' : ULift.{u} (Fin 2)} {a b : C} (hs : s ≤ s') (ha : a ∈ T') (hb : b ∈ T')
    (hab : a ≤ b) (h : R a b ∨ a = b) :
    R (retractionHomotopy r ε s a) (retractionHomotopy r ε s' b) ∨
      retractionHomotopy r ε s a = retractionHomotopy r ε s' b := by
  obtain ⟨h₁, h₂⟩ := hR a ha b hb hab h
  obtain ⟨s⟩ := s
  obtain ⟨s'⟩ := s'
  have hs' : s ≤ s' := hs
  rw [retractionHomotopy, retractionHomotopy]
  fin_cases s <;> fin_cases s' <;> cases ε
  all_goals simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero, cond_false,
    cond_true] at h₂ ⊢
  all_goals first
    | exact h
    | exact h₁
    | exact h₂
    | exact absurd hs' (by decide)

variable {R r ε} in
private def retractionHomotopyMap (hr : ∀ a ∈ T', ∀ b ∈ T', a ≤ b → r a ≤ r b)
    (hrT : ∀ a ∈ T', r a ∈ T) (hT : T ⊆ T') (hle : ∀ a ∈ T', cond ε (r a ≤ a) (a ≤ r a)) :
    (Δ[1] ⊗ (chainSubcomplex T').toSSet : SSet.{u}) ⟶ (chainSubcomplex T').toSSet where
  app k := ↾fun z => ⟨Monotone.functor
    (f := fun j => ULift.up (retractionHomotopy r ε
      (((SSet.stdSimplex.isoNerve 1).hom.app k z.1).obj j) (z.2.1.obj j).down))
    (fun i j h => retractionHomotopy_mono hr hle
      (leOfHom (((SSet.stdSimplex.isoNerve 1).hom.app k z.1).map (homOfLE h)))
      (z.2.2 i) (z.2.2 j) (ULift.down_le.2 (leOfHom (z.2.1.map (homOfLE h))))),
    fun j => retractionHomotopy_mem hrT hT _ (z.2.2 j)⟩
  naturality k m f := by
    ext z
    refine Subtype.ext (nerve.ext_of_isThin (funext fun i => ?_))
    exact congrArg (fun a : (nerve (ULift.{u} (Fin 2))).obj m =>
      ULift.up (retractionHomotopy r ε (a.obj i) (z.2.1.obj _).down))
      (NatTrans.naturality_apply (SSet.stdSimplex.isoNerve 1).hom f z.1)

theorem weakEquivalence_markedSubcomplexMap_chainSubcomplex_of_retraction (hT : T ⊆ T')
    (hr : ∀ a ∈ T', ∀ b ∈ T', a ≤ b → r a ≤ r b) (hrT : ∀ a ∈ T', r a ∈ T)
    (hfix : ∀ a ∈ T, r a = a) (hle : ∀ a ∈ T', cond ε (r a ≤ a) (a ≤ r a))
    (hR : ∀ a ∈ T', ∀ b ∈ T', a ≤ b → (R a b ∨ a = b) →
      (R (r a) (r b) ∨ r a = r b) ∧ cond ε (R (r a) b ∨ r a = b) (R a (r b) ∨ a = r b)) :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (chainSubcomplex_mono hT)) := by
  let ρ : markedSubcomplex (edgeSet.{u} R) (chainSubcomplex T') ⟶
      markedSubcomplex (edgeSet R) (chainSubcomplex T) :=
    edgeHomMk (chainMap r hr hrT) fun e he =>
      (mem_marked_markedSubcomplex_iff R (A := chainSubcomplex T) _).2
        (hR _ (e.2 0) _ (e.2 1) (obj_zero_le_obj_one e.1)
          ((mem_marked_markedSubcomplex_iff R (A := chainSubcomplex T') e).1 he)).1
  let H : sharpEdgeProd.obj (markedSubcomplex (edgeSet.{u} R) (chainSubcomplex T')) ⟶
      markedSubcomplex (edgeSet R) (chainSubcomplex T') :=
    edgeHomMk (retractionHomotopyMap hr hrT hT hle) fun e he =>
      (mem_marked_markedSubcomplex_iff R (A := chainSubcomplex T') _).2
        (retractionHomotopy_rel hR (SSet.stdSimplex.monotone_apply e.1 (Fin.zero_le 1))
          (e.2.2 0) (e.2.2 1) (obj_zero_le_obj_one e.2.1)
          ((mem_marked_markedSubcomplex_iff R (A := chainSubcomplex T') e.2).1
            ((mem_marked_sharpEdgeProdObj _ e).1 he)))
  let i := markedSubcomplexMap (edgeSet R) (chainSubcomplex_mono hT)
  have hiρ : i ≫ ρ = 𝟙 _ := MarkedPresheaf.hom_ext (by
    ext ⟨⟨k⟩⟩ σ
    exact Subtype.ext (nerve.ext_of_isThin (funext fun j => ULift.ext _ _ (hfix _ (σ.2 j)))))
  have hid : (sharpEdgeEndpoint (cond ε 1 0)).app _ ≫ H = 𝟙 _ := MarkedPresheaf.hom_ext (by
    ext ⟨⟨k⟩⟩ σ
    refine Subtype.ext (nerve.ext_of_isThin (funext fun j => ?_))
    cases ε <;> rfl)
  have hρ : (sharpEdgeEndpoint (cond ε 0 1)).app _ ≫ H = ρ ≫ i := MarkedPresheaf.hom_ext (by
    ext ⟨⟨k⟩⟩ σ
    refine Subtype.ext (nerve.ext_of_isThin (funext fun j => ?_))
    cases ε <;> rfl)
  have := weakEquivalence_of_sharpEdgeHomotopy ρ i hiρ H hid hρ
  have : WeakEquivalence (i ≫ ρ) := by
    rw [hiρ]
    infer_instance
  exact weakEquivalence_of_postcomp i ρ

end Retraction

section ConeTop

open MonoidalCategory

variable {Λ : Set C} {u w : C}

open scoped Classical in
variable (w) in
private noncomputable def coneTopLevel (a : C) : Fin 3 :=
  if a = w then 2 else 0

open scoped Classical in
variable (u w) in
private noncomputable def coneTopRetraction (a : C) (k : ULift.{u} (Fin 3)) : C :=
  if k.down = 0 then (if a = w then u else a) else if k.down = 1 then u else
    (if a = w then w else u)

omit [PartialOrder C] in
private theorem mem_of_mem_insert_of_ne {a : C} (ha : a ∈ insert w Λ) (h : a ≠ w) : a ∈ Λ :=
  (Set.mem_insert_iff.1 ha).resolve_left h

private theorem eq_of_mem_insert_of_le (hΛw : ∀ a ∈ Λ, a ≤ w) (hw : w ∉ Λ) {b : C}
    (hb : b ∈ insert w Λ) (h : w ≤ b) : b = w := by
  by_contra hne
  exact hw ((le_antisymm h (hΛw b (mem_of_mem_insert_of_ne hb hne))) ▸
    mem_of_mem_insert_of_ne hb hne)

private theorem coneTopLevel_mono (hΛw : ∀ a ∈ Λ, a ≤ w) (hw : w ∉ Λ) {a b : C}
    (hb : b ∈ insert w Λ) (hab : a ≤ b) : coneTopLevel w a ≤ coneTopLevel w b := by
  rw [coneTopLevel, coneTopLevel]
  by_cases ha : a = w
  · rw [if_pos ha, if_pos (eq_of_mem_insert_of_le hΛw hw hb (ha ▸ hab))]
  · rw [if_neg ha]
    exact Fin.zero_le _

private theorem coneTopRetraction_mono (hΛu : ∀ a ∈ Λ, a ≤ u) (hu : u ∈ Λ)
    (hΛw : ∀ a ∈ Λ, a ≤ w) (hw : w ∉ Λ) {a b : C} (ha : a ∈ insert w Λ) (hb : b ∈ insert w Λ)
    (hab : a ≤ b) {k l : ULift.{u} (Fin 3)} (hkl : k ≤ l) :
    coneTopRetraction u w a k ≤ coneTopRetraction u w b l := by
  obtain ⟨k⟩ := k
  obtain ⟨l⟩ := l
  have hkl' : k ≤ l := hkl
  have huw := hΛw u hu
  rw [coneTopRetraction, coneTopRetraction]
  by_cases haw : a = w
  · obtain rfl := eq_of_mem_insert_of_le hΛw hw hb (haw ▸ hab)
    subst haw
    fin_cases k <;> fin_cases l
    all_goals simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, Fin.reduceFinMk,
      one_ne_zero, Fin.reduceEq, le_refl]
    all_goals first | exact huw | exact absurd hkl' (by decide)
  · have haΛ := hΛu a (mem_of_mem_insert_of_ne ha haw)
    by_cases hbw : b = w
    · subst hbw
      fin_cases k <;> fin_cases l
      all_goals simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, Fin.reduceFinMk,
        one_ne_zero, Fin.reduceEq, haw, le_refl]
      all_goals first | exact haΛ | exact huw | exact haΛ.trans huw
    · fin_cases k <;> fin_cases l
      all_goals simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, Fin.reduceFinMk,
        one_ne_zero, Fin.reduceEq, haw, hbw, le_refl]
      all_goals first | exact hab | exact haΛ | exact hΛu b (mem_of_mem_insert_of_ne hb hbw) |
        exact absurd hkl' (by decide)

omit [PartialOrder C] in
private theorem coneTopRetraction_mem_of_mem (hu : u ∈ Λ) (hw : w ∉ Λ) {a : C} (ha : a ∈ Λ)
    (k : ULift.{u} (Fin 3)) : coneTopRetraction u w a k ∈ Λ := by
  have haw : a ≠ w := fun h => hw (h ▸ ha)
  rw [coneTopRetraction]
  split_ifs <;> first | exact ha | exact hu

omit [PartialOrder C] in
private theorem coneTopRetraction_mem_pair {a : C} (ha : a ∈ ({u, w} : Set C))
    (k : ULift.{u} (Fin 3)) : coneTopRetraction u w a k ∈ ({u, w} : Set C) := by
  rw [coneTopRetraction]
  split_ifs <;> first | exact ha | exact Or.inl rfl | exact Or.inr rfl

omit [PartialOrder C] in
private theorem coneTopRetraction_mem_of_ne_two (hu : u ∈ Λ) {a : C} (ha : a ∈ insert w Λ)
    {k : ULift.{u} (Fin 3)} (hk : k.down ≠ 2) : coneTopRetraction u w a k ∈ Λ := by
  rw [coneTopRetraction]
  split_ifs with h₀ h₁ h₂
  · exact hu
  · exact mem_of_mem_insert_of_ne ha h₁
  · exact hu
  · exact absurd (by omega : k.down = 2) hk
  · exact hu

omit [PartialOrder C] in
private theorem coneTopRetraction_mem_of_ne_zero {a : C} {k : ULift.{u} (Fin 3)}
    (hk : k.down ≠ 0) : coneTopRetraction u w a k ∈ ({u, w} : Set C) := by
  rw [coneTopRetraction]
  split_ifs <;> first | exact absurd ‹_› hk | exact Or.inl rfl | exact Or.inr rfl

omit [PartialOrder C] in
private theorem coneTopRetraction_mem (hu : u ∈ Λ) {a : C} (ha : a ∈ insert w Λ)
    (k : ULift.{u} (Fin 3)) : coneTopRetraction u w a k ∈ insert w Λ := by
  rw [coneTopRetraction]
  split_ifs <;> first | exact ha | exact Set.mem_insert_of_mem _ hu | exact Set.mem_insert _ _

omit [PartialOrder C] in
private theorem coneTopRetraction_coneTopLevel (a : C) :
    coneTopRetraction.{u} u w a (ULift.up (coneTopLevel w a)) = a := by
  rw [coneTopRetraction, coneTopLevel]
  by_cases h : a = w
  · subst h
    simp
  · simp [h]

variable (Λ u w) in
def coneBase : (nerve (ULift.{u} C)).Subcomplex :=
  chainSubcomplex Λ ⊔ chainSubcomplex {u, w}

theorem coneBase_le (hu : u ∈ Λ) : coneBase.{u} Λ u w ≤ chainSubcomplex (insert w Λ) :=
  sup_le (chainSubcomplex_mono (Set.subset_insert _ _))
    (chainSubcomplex_mono (Set.insert_subset (Set.mem_insert_of_mem _ hu)
      (Set.singleton_subset_iff.2 (Set.mem_insert _ _))))

private theorem innerAnodyneExtensions_coneBase (hΛu : ∀ a ∈ Λ, a ≤ u) (hu : u ∈ Λ)
    (hΛw : ∀ a ∈ Λ, a ≤ w) (hw : w ∉ Λ) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE (coneBase_le.{u} (Λ := Λ) (w := w) hu)) := by
  let B := chainSubcomplex (insert w Λ)
  let A := coneBase Λ u w
  let A' := A.preimage B.ι
  let lev : B.toSSet ⟶ Δ[2] :=
    chainMap (T' := (Set.univ : Set (Fin 3))) (coneTopLevel w)
      (fun _ _ _ hb hab => coneTopLevel_mono hΛw hw hb hab) (fun _ _ => trivial) ≫
      (chainSubcomplex Set.univ).ι ≫ (SSet.stdSimplex.isoNerve 2).inv
  let s₂ : B.toSSet ⟶ B.toSSet ⊗ Δ[2] := CartesianMonoidalCategory.lift (𝟙 _) lev
  let r₂ : B.toSSet ⊗ Δ[2] ⟶ B.toSSet :=
    { app k := ↾fun z => ⟨Monotone.functor
        (f := fun j => ULift.up (coneTopRetraction u w (z.1.1.obj j).down
          (((SSet.stdSimplex.isoNerve 2).hom.app k z.2).obj j)))
        (fun i j h => coneTopRetraction_mono hΛu hu hΛw hw (z.1.2 i) (z.1.2 j)
          (ULift.down_le.2 (leOfHom (z.1.1.map (homOfLE h))))
          (leOfHom (((SSet.stdSimplex.isoNerve 2).hom.app k z.2).map (homOfLE h)))),
        fun j => coneTopRetraction_mem hu (z.1.2 j) _⟩
      naturality k m f := by
        ext z
        refine Subtype.ext (nerve.ext_of_isThin (funext fun i => ?_))
        exact congrArg (fun a : (nerve (ULift.{u} (Fin 3))).obj m =>
          ULift.up (coneTopRetraction u w (z.1.1.obj _).down (a.obj i)))
          (NatTrans.naturality_apply (SSet.stdSimplex.isoNerve 2).hom f z.2) }
  let s₁ : A.toSSet ⟶ (A'.unionProd Λ[2, 1]).toSSet :=
    SSet.Subcomplex.lift (SSet.Subcomplex.homOfLE (coneBase_le hu) ≫ s₂) (by
      rintro _ _ ⟨y, rfl⟩
      exact (SSet.Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr y.2))
  let r₁ : (A'.unionProd Λ[2, 1]).toSSet ⟶ A.toSSet :=
    SSet.Subcomplex.lift ((A'.unionProd Λ[2, 1]).ι ≫ r₂ ≫ B.ι) (by
      rintro ⟨⟨d⟩⟩ _ ⟨⟨⟨σ, τ⟩, hy⟩, rfl⟩
      rcases (SSet.Subcomplex.mem_unionProd_iff _ _ _).1 hy with hτ | hσ
      · obtain ⟨m, hm1, hm⟩ := (SSet.mem_horn_iff_notMem_range τ 1).1 hτ
        fin_cases m
        · refine Or.inr fun j => coneTopRetraction_mem_of_ne_zero fun h => hm ⟨j, ?_⟩
          exact h
        · exact absurd rfl hm1
        · refine Or.inl fun j => coneTopRetraction_mem_of_ne_two hu (σ.2 j) fun h => hm ⟨j, ?_⟩
          exact h
      · rcases hσ with hσ | hσ
        · exact Or.inl fun j => coneTopRetraction_mem_of_mem hu hw (hσ j) _
        · exact Or.inr fun j => coneTopRetraction_mem_pair (hσ j) _)
  let R : RetractArrow (SSet.Subcomplex.homOfLE (coneBase_le (Λ := Λ) (w := w) hu))
      (A'.unionProd Λ[2, 1]).ι :=
    { i := Arrow.homMk s₁ s₂ rfl
      r := Arrow.homMk r₁ r₂ rfl
      retract := Arrow.hom_ext _ _ (by
          ext ⟨⟨d⟩⟩ σ
          exact Subtype.ext (nerve.ext_of_isThin (funext fun j =>
            ULift.ext _ _ (coneTopRetraction_coneTopLevel _))))
        (by
          ext ⟨⟨d⟩⟩ σ
          exact Subtype.ext (nerve.ext_of_isThin (funext fun j =>
            ULift.ext _ _ (coneTopRetraction_coneTopLevel _)))) }
  exact MorphismProperty.of_retract R (SSet.innerAnodyneExtensions_unionProd_ι _ _
    (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide)))

end ConeTop

section Final

variable (R : C → C → Prop) {Λ : Set C} {t u w : C}

theorem weakEquivalence_coneBase_of_le (hΛu : ∀ a ∈ Λ, a ≤ u) (hu : u ∈ Λ)
    (hΛw : ∀ a ∈ Λ, a ≤ w) (hw : w ∉ Λ) (hR : ∀ a, R a w → a = w) :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (coneBase_le (Λ := Λ) (w := w) hu)) :=
  weakEquivalence_markedSubcomplexMap_of_innerAnodyneExtensions _ _
    (innerAnodyneExtensions_coneBase hΛu hu hΛw hw) fun e he => by
      by_cases h₁ : (e.1.obj 1).down = w
      · have he' : R (e.1.obj 0).down (e.1.obj 1).down := he
        rw [h₁] at he'
        have h₀ : (e.1.obj 0).down = w := hR _ he'
        refine Or.inr fun j => ?_
        fin_cases j
        · exact Or.inr h₀
        · exact Or.inr h₁
      · have h₁Λ := mem_of_mem_insert_of_ne (e.2 1) h₁
        have h₀ : (e.1.obj 0).down ≠ w := fun h => by
          have hle := obj_zero_le_obj_one e.1
          rw [h] at hle
          exact h₁ (eq_of_mem_insert_of_le hΛw hw (e.2 1) hle)
        refine Or.inl fun j => ?_
        fin_cases j
        · exact mem_of_mem_insert_of_ne (e.2 0) h₀
        · exact h₁Λ

open scoped Classical in
theorem weakEquivalence_chainSubcomplex_collapse {T T' : Set C}
    (hT : ∀ a, a ∈ T ↔ a ∈ T' ∧ a ≠ u) (ht : t ∈ T') (htu : t ≠ u) (hle : t ≤ u)
    (hRtu : R t u) (hlo : ∀ a ∈ T', a ≠ u → a ≤ u → a ≤ t ∧ (R a u → R a t ∨ a = t))
    (hhi : ∀ a ∈ T', a ≠ u → u ≤ a → t ≤ a ∧ (R u a → R t a ∨ t = a)) :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (chainSubcomplex_mono (fun a ha => ((hT a).1 ha).1 : T ⊆ T'))) := by
  refine weakEquivalence_markedSubcomplexMap_chainSubcomplex_of_retraction R
    (fun a => if a = u then t else a) true (fun a ha => ((hT a).1 ha).1)
    (fun a ha b hb hab => ?_) (fun a ha => ?_)
    (fun a ha => if_neg ((hT a).1 ha).2) (fun a ha => ?_) (fun a ha b hb hab h => ?_)
  · by_cases hau : a = u <;> by_cases hbu : b = u
    · simp only [hau, hbu, ↓reduceIte, le_refl]
    · simp only [hau, hbu, ↓reduceIte]
      exact (hhi b hb hbu (hau ▸ hab)).1
    · simp only [hau, hbu, ↓reduceIte]
      exact (hlo a ha hau (hbu ▸ hab)).1
    · simp only [hau, hbu, ↓reduceIte]
      exact hab
  · by_cases hau : a = u
    · simp only [hau, ↓reduceIte]
      exact (hT t).2 ⟨ht, htu⟩
    · simp only [hau, ↓reduceIte]
      exact (hT a).2 ⟨ha, hau⟩
  · by_cases hau : a = u
    · simp only [hau, ↓reduceIte, cond_true]
      exact hle
    · simp only [hau, ↓reduceIte, cond_true, le_refl]
  · by_cases hau : a = u <;> by_cases hbu : b = u
    · subst hau hbu
      simp only [↓reduceIte, cond_true, or_true]
      exact ⟨trivial, Or.inl hRtu⟩
    · subst hau
      simp only [↓reduceIte, hbu, cond_true, and_self]
      rcases h with h | h
      · exact (hhi b hb hbu hab).2 h
      · exact absurd h.symm hbu
    · subst hbu
      simp only [↓reduceIte, hau, cond_true]
      rcases h with h | h
      · exact ⟨(hlo a ha hau hab).2 h, Or.inl h⟩
      · exact absurd h hau
    · simp only [hau, hbu, ↓reduceIte, cond_true, and_self]
      exact h

theorem weakEquivalence_coneBase_of_edge (htΛ : t ∈ Λ) (huΛ : u ∈ Λ) (htu : t ≤ u)
    (hRtu : R t u) (hΛw : ∀ a ∈ Λ, a ≤ w) (hw : w ∉ Λ) (hR : ∀ a, R a w → a = w)
    [WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (coneBase_le (Λ := Λ) (w := w) huΛ))] :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (coneBase_le (Λ := Λ) (w := w) htΛ)) := by
  by_cases htu' : t = u
  · subst htu'
    infer_instance
  have hwt : w ≠ t := fun h => hw (h ▸ htΛ)
  have hwu : w ≠ u := fun h => hw (h ▸ huΛ)
  have huw : u ≤ w := hΛw u huΛ
  have htw : t ≤ w := hΛw t htΛ
  let P : Set C := insert w {t, u}
  have hP : ∀ a, a ∈ P ↔ a = w ∨ a = t ∨ a = u := fun _ => Iff.rfl
  have hU : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (le_sup_left : coneBase Λ u w ≤ coneBase Λ u w ⊔ chainSubcomplex P)) := by
    have hinf : coneBase.{u} Λ u w ⊓ chainSubcomplex P = coneBase {t, u} u w := by
      rw [coneBase, chainSubcomplex_sup_inf, coneBase]
      congr 2
      · ext a
        simp only [Set.mem_inter_iff, hP, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨ha, rfl | rfl | rfl⟩
          · exact absurd ha hw
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨htΛ, Or.inr (Or.inl rfl)⟩
          · exact ⟨huΛ, Or.inr (Or.inr rfl)⟩
      · ext a
        simp only [Set.mem_inter_iff, hP, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · exact fun h => h.1
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩
          · exact ⟨Or.inr rfl, Or.inl rfl⟩
    have sq : (coneBase.{u} {t, u} u w).BicartSq (coneBase Λ u w) (chainSubcomplex P)
        (coneBase Λ u w ⊔ chainSubcomplex P) := ⟨rfl, hinf⟩
    have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq.le₁₃) :=
      weakEquivalence_coneBase_of_le R (Λ := {t, u}) (u := u) (w := w)
        (fun a ha => by rcases ha with rfl | rfl; exacts [htu, le_refl _]) (Or.inr rfl)
        (fun a ha => by rcases ha with rfl | rfl; exacts [htw, huw])
        (fun h => by rcases h with h | h; exacts [hwt h, hwu h]) hR
    exact weakEquivalence_markedSubcomplexMap_of_bicartSq _ sq
  have hPw : ({t, w} : Set C) ⊆ P := Set.insert_subset (Or.inr (Or.inl rfl))
    (Set.singleton_subset_iff.2 (Or.inl rfl))
  have hT₁ : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (chainSubcomplex_mono (Set.singleton_subset_iff.2 (Or.inl rfl) : ({t} : Set C) ⊆ {t, u}))) :=
    weakEquivalence_chainSubcomplex_collapse R (T' := {t, u})
      (fun a => ⟨fun h => ⟨Or.inl h, fun hau => htu' (h ▸ hau)⟩,
        fun ⟨h, hau⟩ => h.resolve_right hau⟩)
      (Or.inl rfl) htu' htu hRtu
      (fun a ha hau _ => by
        obtain rfl := ha.resolve_right hau
        exact ⟨le_refl _, fun _ => Or.inr rfl⟩)
      (fun a ha hau _ => by
        obtain rfl := ha.resolve_right hau
        exact ⟨le_refl _, fun _ => Or.inr rfl⟩)
  have sq₁ : (chainSubcomplex.{u} ({t} : Set C)).BicartSq (chainSubcomplex {t, w})
      (chainSubcomplex {t, u}) (coneBase {t, u} t w) := by
    refine ⟨sup_comm _ _, ?_⟩
    rw [← chainSubcomplex_inter]
    congr 1
    ext a
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · rcases h with h | h
        · exact absurd h hwt
        · exact absurd h hwu
    · rintro rfl
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq₁.le₁₃) := hT₁
  have h₂ := weakEquivalence_markedSubcomplexMap_of_bicartSq (edgeSet R) sq₁
  have h₃ : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (chainSubcomplex_mono hPw)) :=
    weakEquivalence_chainSubcomplex_collapse R (T' := P)
      (fun a => ⟨fun h => ⟨hPw h, fun hau => by
          rcases h with rfl | rfl
          · exact htu' hau
          · exact hwu hau⟩,
        fun ⟨h, hau⟩ => by
          rcases h with rfl | rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl rfl
          · exact absurd rfl hau⟩)
      (Or.inr (Or.inl rfl)) htu' htu hRtu
      (fun a ha hau hau' => by
        rcases ha with rfl | rfl | rfl
        · exact absurd (le_antisymm huw hau') hwu.symm
        · exact ⟨le_refl _, fun _ => Or.inr rfl⟩
        · exact absurd rfl hau)
      (fun a ha hau hau' => by
        rcases ha with rfl | rfl | rfl
        · exact ⟨htw, fun h => absurd (hR _ h) hwu.symm⟩
        · exact ⟨le_refl _, fun _ => Or.inr rfl⟩
        · exact absurd rfl hau)
  have hle₁ : coneBase.{u} {t, u} t w ≤ chainSubcomplex P := coneBase_le (Or.inl rfl)
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq₁.le₂₄ ≫
      markedSubcomplexMap (edgeSet R) hle₁) := by
    rw [markedSubcomplexMap_comp]
    exact h₃
  have h₄ := weakEquivalence_of_precomp (markedSubcomplexMap (edgeSet R) sq₁.le₂₄)
    (markedSubcomplexMap (edgeSet R) hle₁)
  have hD : coneBase.{u} Λ u w ⊔ chainSubcomplex P = coneBase Λ t w ⊔ chainSubcomplex P := by
    have h₁ : chainSubcomplex.{u} ({u, w} : Set C) ≤ chainSubcomplex P :=
      chainSubcomplex_mono (Set.insert_subset (Or.inr (Or.inr rfl))
        (Set.singleton_subset_iff.2 (Or.inl rfl)))
    rw [coneBase, coneBase, sup_assoc, sup_eq_right.2 h₁, sup_assoc,
      sup_eq_right.2 (chainSubcomplex_mono hPw)]
  have hinf₂ : coneBase.{u} Λ t w ⊓ chainSubcomplex P = coneBase {t, u} t w := by
    rw [coneBase, chainSubcomplex_sup_inf, coneBase]
    congr 2
    · ext a
      simp only [Set.mem_inter_iff, hP, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ha, rfl | rfl | rfl⟩
        · exact absurd ha hw
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨htΛ, Or.inr (Or.inl rfl)⟩
        · exact ⟨huΛ, Or.inr (Or.inr rfl)⟩
    · ext a
      simp only [Set.mem_inter_iff, hP, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
        · exact ⟨Or.inr rfl, Or.inl rfl⟩
  have sq₂ : (coneBase.{u} {t, u} t w).BicartSq (coneBase Λ t w) (chainSubcomplex P)
      (coneBase Λ u w ⊔ chainSubcomplex P) := ⟨hD.symm, hinf₂⟩
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq₂.le₁₃) := h₄
  have hT := weakEquivalence_markedSubcomplexMap_of_bicartSq (edgeSet R) sq₂
  have hDC : coneBase.{u} Λ u w ⊔ chainSubcomplex P ≤ chainSubcomplex (insert w Λ) :=
    sup_le (coneBase_le huΛ) (chainSubcomplex_mono (Set.insert_subset (Set.mem_insert _ _)
      (Set.insert_subset (Set.mem_insert_of_mem _ htΛ)
        (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ huΛ)))))
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (le_sup_left : coneBase Λ u w ≤ coneBase Λ u w ⊔ chainSubcomplex P) ≫
      markedSubcomplexMap (edgeSet R) hDC) := by
    rw [markedSubcomplexMap_comp]
    infer_instance
  have := weakEquivalence_of_precomp (markedSubcomplexMap (edgeSet R)
    (le_sup_left : coneBase Λ u w ≤ coneBase Λ u w ⊔ chainSubcomplex P))
    (markedSubcomplexMap (edgeSet R) hDC)
  have e := markedSubcomplexMap_comp (edgeSet R) sq₂.le₂₄ hDC
  rw [← e]
  infer_instance

theorem coneBase_inf_chainSubcomplex {A B : Set C} (hw : w ∉ A) (ht : t ∈ B) :
    coneBase.{u} A t w ⊓ chainSubcomplex (insert w B) = coneBase (A ∩ B) t w := by
  rw [coneBase, chainSubcomplex_sup_inf, coneBase]
  congr 2
  · ext a
    simp only [Set.mem_inter_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨ha, rfl | hb⟩
      · exact absurd ha hw
      · exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨ha, Or.inr hb⟩
  · ext a
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, Or.inr ht⟩
      · exact ⟨Or.inr rfl, Or.inl rfl⟩

theorem chainSubcomplex_insert_inf (A B : Set C) :
    chainSubcomplex.{u} (insert w A) ⊓ chainSubcomplex (insert w B) =
      chainSubcomplex (insert w (A ∩ B)) := by
  rw [← chainSubcomplex_inter, Set.insert_inter_distrib]

theorem chainSubcomplex_insert_sup {A B : Set C}
    (h : ∀ a ∈ A, ∀ b ∈ B, a ≤ b ∨ b ≤ a → a ∈ B ∨ b ∈ A) :
    chainSubcomplex.{u} (insert w A) ⊔ chainSubcomplex (insert w B) =
      chainSubcomplex (insert w (A ∪ B)) := by
  rw [Set.insert_union_distrib, chainSubcomplex_union]
  rintro a (rfl | ha) b (rfl | hb) hab
  · exact Or.inl (Set.mem_insert _ _)
  · exact Or.inl (Set.mem_insert _ _)
  · exact Or.inr (Set.mem_insert _ _)
  · rcases h a ha b hb hab with h' | h'
    · exact Or.inl (Set.mem_insert_of_mem _ h')
    · exact Or.inr (Set.mem_insert_of_mem _ h')

theorem weakEquivalence_coneBase_singleton (x : C) :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (coneBase_le (Λ := {x}) (w := w) (Set.mem_singleton x))) := by
  refine weakEquivalence_markedSubcomplexMap_of_eq _ ?_
  rw [coneBase, sup_eq_right.2 (chainSubcomplex_mono
    (Set.singleton_subset_iff.2 (Set.mem_insert x {w}) : ({x} : Set C) ⊆ {x, w}))]
  congr 1
  ext a
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem weakEquivalence_coneBase_union {V W : Set C} (htV : t ∈ V) (htW : t ∈ W)
    (hwV : w ∉ V) (hwW : w ∉ W) (hVW : ∀ a ∈ V, ∀ b ∈ W, a ≤ b ∨ b ≤ a → a ∈ W ∨ b ∈ V)
    [WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (coneBase_le (Λ := V) (w := w) htV))]
    [WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (coneBase_le (Λ := W) (w := w) htW))]
    [WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (coneBase_le (Λ := V ∩ W) (w := w) ⟨htV, htW⟩))] :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (coneBase_le (Λ := V ∪ W) (w := w) (Or.inl htV))) := by
  have hwΛ : w ∉ V ∪ W := fun h => h.elim hwV hwW
  have sq₁ : (coneBase.{u} V t w).BicartSq (coneBase (V ∪ W) t w) (chainSubcomplex (insert w V))
      (coneBase (V ∪ W) t w ⊔ chainSubcomplex (insert w V)) := by
    refine ⟨rfl, ?_⟩
    rw [coneBase_inf_chainSubcomplex hwΛ htV, Set.union_inter_cancel_left]
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq₁.le₁₃) := ‹_›
  have h₁ := weakEquivalence_markedSubcomplexMap_of_bicartSq (edgeSet R) sq₁
  have sq₃ : (coneBase.{u} (V ∩ W) t w).BicartSq (coneBase W t w)
      (chainSubcomplex (insert w (V ∩ W)))
      (coneBase W t w ⊔ chainSubcomplex (insert w (V ∩ W))) := by
    refine ⟨rfl, ?_⟩
    rw [coneBase_inf_chainSubcomplex (B := V ∩ W) hwW ⟨htV, htW⟩, Set.inter_comm V W,
      ← Set.inter_assoc, Set.inter_self]
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq₃.le₁₃) := ‹_›
  have h₃ := weakEquivalence_markedSubcomplexMap_of_bicartSq (edgeSet R) sq₃
  have hle₃ : coneBase.{u} W t w ⊔ chainSubcomplex (insert w (V ∩ W)) ≤
      chainSubcomplex (insert w W) :=
    sup_le (coneBase_le htW) (chainSubcomplex_mono (Set.insert_subset_insert
      Set.inter_subset_right))
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq₃.le₂₄ ≫
      markedSubcomplexMap (edgeSet R) hle₃) := by
    rw [markedSubcomplexMap_comp]
    infer_instance
  have h₃' := weakEquivalence_of_precomp (markedSubcomplexMap (edgeSet R) sq₃.le₂₄)
    (markedSubcomplexMap (edgeSet R) hle₃)
  have sq₂ : (coneBase.{u} W t w ⊔ chainSubcomplex (insert w (V ∩ W))).BicartSq
      (coneBase (V ∪ W) t w ⊔ chainSubcomplex (insert w V)) (chainSubcomplex (insert w W))
      (chainSubcomplex (insert w (V ∪ W))) := by
    refine ⟨?_, ?_⟩
    · rw [sup_assoc, chainSubcomplex_insert_sup hVW]
      exact sup_eq_right.2 (coneBase_le (Or.inl htV))
    · rw [sup_inf_right', coneBase_inf_chainSubcomplex hwΛ htW, Set.union_inter_cancel_right,
        chainSubcomplex_insert_inf]
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq₂.le₁₃) := h₃'
  have h₂ := weakEquivalence_markedSubcomplexMap_of_bicartSq (edgeSet R) sq₂
  have e := markedSubcomplexMap_comp (edgeSet R) sq₁.le₂₄ sq₂.le₂₄
  rw [← e]
  infer_instance

theorem weakEquivalence_coneBase_union_of_inter_eq {V W : Set C} {a : C} (haV : a ∈ V)
    (htW : t ∈ W) (hVWa : V ∩ W = {a}) (hwV : w ∉ V) (hwW : w ∉ W)
    (hVW : ∀ a ∈ V, ∀ b ∈ W, a ≤ b ∨ b ≤ a → a ∈ W ∨ b ∈ V)
    [WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (coneBase_le (Λ := V) (w := w) haV))]
    [WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (coneBase_le (Λ := W) (w := w) htW))] :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (coneBase_le (Λ := V ∪ W) (w := w) (Or.inr htW))) := by
  have hwΛ : w ∉ V ∪ W := fun h => h.elim hwV hwW
  have sq₁ : (coneBase.{u} W t w).BicartSq (coneBase (V ∪ W) t w) (chainSubcomplex (insert w W))
      (coneBase (V ∪ W) t w ⊔ chainSubcomplex (insert w W)) := by
    refine ⟨rfl, ?_⟩
    rw [coneBase_inf_chainSubcomplex hwΛ htW, Set.union_inter_cancel_right]
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq₁.le₁₃) := ‹_›
  have h₁ := weakEquivalence_markedSubcomplexMap_of_bicartSq (edgeSet R) sq₁
  have hinf : (coneBase.{u} (V ∪ W) t w ⊔ chainSubcomplex (insert w W)) ⊓
      chainSubcomplex (insert w V) = coneBase V a w := by
    rw [sup_inf_right', coneBase, chainSubcomplex_sup_inf, chainSubcomplex_insert_inf,
      Set.inter_comm W V, hVWa, coneBase]
    have hΛV : (V ∪ W) ∩ insert w V = V := by
      rw [Set.inter_insert_of_notMem hwΛ, Set.union_inter_cancel_left]
    have hta : ({t, w} : Set C) ∩ insert w V ⊆ {a, w} := by
      rintro b ⟨hb₁ | hb₁, hb₂⟩
      · subst hb₁
        rcases hb₂ with h | h
        · exact absurd (h ▸ htW) hwW
        · exact Or.inl ((Set.ext_iff.1 hVWa b).1 ⟨h, htW⟩)
      · exact Or.inr hb₁
    have hwa : (insert w {a} : Set C) = {a, w} := Set.pair_comm w a
    rw [hΛV, hwa]
    refine le_antisymm (sup_le (sup_le le_sup_left (le_sup_of_le_right
      (chainSubcomplex_mono hta))) le_sup_right) (sup_le (le_sup_of_le_left le_sup_left)
      le_sup_right)
  have sq₂ : (coneBase.{u} V a w).BicartSq (coneBase (V ∪ W) t w ⊔ chainSubcomplex (insert w W))
      (chainSubcomplex (insert w V)) (chainSubcomplex (insert w (V ∪ W))) := by
    refine ⟨?_, hinf⟩
    rw [sup_assoc, sup_comm (chainSubcomplex (insert w W)), chainSubcomplex_insert_sup hVW]
    exact sup_eq_right.2 (coneBase_le (Or.inr htW))
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) sq₂.le₁₃) := ‹_›
  have h₂ := weakEquivalence_markedSubcomplexMap_of_bicartSq (edgeSet R) sq₂
  have e := markedSubcomplexMap_comp (edgeSet R) sq₁.le₂₄ sq₂.le₂₄
  rw [← e]
  infer_instance

theorem weakEquivalence_coneBase_congr {Λ Λ' : Set C} (h : Λ = Λ') (ht : t ∈ Λ)
    [WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (coneBase_le (Λ := Λ) (w := w) ht))] :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (coneBase_le (Λ := Λ') (w := w) (h ▸ ht))) := by
  subst h
  infer_instance

end Final

end Chains

section Molecule

open Order

variable {P : OGP.{0}} (R : P → P → Prop) {w : P}

theorem mem_or_mem_of_le_or_le {V W : LowerSet P} : ∀ a ∈ (V : Set P), ∀ b ∈ (W : Set P),
    a ≤ b ∨ b ≤ a → a ∈ (W : Set P) ∨ b ∈ (V : Set P) := by
  rintro a ha b hb (hab | hab)
  · exact Or.inl (W.lower hab hb)
  · exact Or.inr (V.lower hab ha)

theorem weakEquivalence_coneBase_of_isMoleculeIn
    (hR₁ : ∀ a b, a ≤ b → b < w →
      P.boundary (.Iic a) 0 true = P.boundary (.Iic b) 0 true → R a b)
    (hR₂ : ∀ a, R a w → a = w) {U : LowerSet P} (hU : IsMoleculeIn P U)
    (hUw : ∀ y ∈ U, y < w) {t : P} (ht : t ∈ P.boundary U 0 true) :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (coneBase_le (Λ := (U : Set P)) (w := w) (boundary_le U 0 true ht))) := by
  suffices h : ∀ n : ℕ, ∀ U, IsMoleculeIn P U → krullDim U ≤ n → (∀ y ∈ U, y < w) →
      ∀ t, t ∈ P.boundary U 0 true → ∀ htU : t ∈ (U : Set P),
        WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
          (coneBase_le (Λ := (U : Set P)) (w := w) htU)) by
    obtain ⟨m, hm⟩ := hU.exists_krullDim_eq
    exact h m U hU hm.le hUw t ht (boundary_le U 0 true ht)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro U hU
  induction hU with
  | point x hx =>
    intro _ _ t ht _
    obtain rfl : t = x := hx.eq_of_le (LowerSet.mem_Iic_iff.1 (boundary_le _ 0 true ht))
    have := weakEquivalence_coneBase_singleton R (w := w) t
    exact weakEquivalence_coneBase_congr R ((LowerSet.coe_Iic t).trans hx.Iic_eq).symm
      (Set.mem_singleton t)
  | atom u hround hbdry ihb =>
    intro _ hUw t ht _
    have hUmol : IsMoleculeIn P (LowerSet.Iic u) := IsMoleculeIn.atom u hround hbdry
    have hΛu : ∀ a ∈ ((LowerSet.Iic u : LowerSet P) : Set P), a ≤ u := fun _ ha => ha
    have huU : u ∈ ((LowerSet.Iic u : LowerSet P) : Set P) := le_refl u
    have htU : t ∈ ((LowerSet.Iic u : LowerSet P) : Set P) := boundary_le _ 0 true ht
    have hw : w ∉ ((LowerSet.Iic u : LowerSet P) : Set P) := fun h => lt_irrefl _ (hUw w h)
    have := weakEquivalence_coneBase_of_le R hΛu huU (fun a ha => (hUw a ha).le) hw hR₂
    obtain ⟨v, hv, hbv⟩ := exists_boundary_zero_eq_Iic hUmol true
    have htv : t ≤ v := LowerSet.mem_Iic_iff.1 (hbv ▸ ht)
    obtain rfl : t = v := le_antisymm htv (hv htv)
    have hRtu : R t u := hR₁ t u (hΛu t htU) (hUw u huU) (by
      rw [hbv]
      exact boundary_Iic_of_isMin hv 0 true)
    exact weakEquivalence_coneBase_of_edge R htU huU (hΛu t htU) hRtu
      (fun a ha => (hUw a ha).le) hw hR₂
  | paste k V W U hpaste hV hW hk ihV ihW =>
    intro hn hUw t ht _
    have hgV := IsMoleculeIn.isGlobular hV
    have hgW := IsMoleculeIn.isGlobular hW
    have hVU : krullDim V ≤ n := (LowerSet.krullDim_mono hpaste.left_le).trans hn
    have hWU : krullDim W ≤ n := (LowerSet.krullDim_mono hpaste.right_le).trans hn
    have hVw : ∀ y ∈ V, y < w := fun y hy => hUw y (hpaste.left_le hy)
    have hWw : ∀ y ∈ W, y < w := fun y hy => hUw y (hpaste.right_le hy)
    have hUVW : ((V : Set P) ∪ W) = U := by
      rw [← LowerSet.coe_sup, hpaste.sup_eq]
    have hwV : w ∉ (V : Set P) := fun h => lt_irrefl _ (hVw w h)
    have hwW : w ∉ (W : Set P) := fun h => lt_irrefl _ (hWw w h)
    have htW : t ∈ P.boundary W 0 true := by
      have h := hpaste.boundary_eq_of_le_cond true hgV hgW (Nat.zero_le k)
      rw [h] at ht
      exact ht
    have := ihW hWU hWw t htW (boundary_le W 0 true htW)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · obtain ⟨a, ha, hba⟩ := exists_boundary_zero_eq_Iic hV true
      have haV : a ∈ P.boundary V 0 true := hba ▸ LowerSet.mem_Iic_iff.2 le_rfl
      have := ihV hVU hVw a haV (boundary_le V 0 true haV)
      have hinter : (V : Set P) ∩ W = {a} := by
        rw [← LowerSet.coe_inf, hpaste.inf_eq_output, hba, LowerSet.coe_Iic, ha.Iic_eq]
      have := weakEquivalence_coneBase_union_of_inter_eq R (w := w)
        (boundary_le V 0 true haV) (boundary_le W 0 true htW) hinter
        hwV hwW mem_or_mem_of_le_or_le
      exact weakEquivalence_coneBase_congr R hUVW
        (Or.inr (boundary_le W 0 true htW))
    · have htV : t ∈ P.boundary V 0 true := by
        rw [← hpaste.boundary_eq_of_lt_cond false hgW hgV hk0 true]
        exact ht
      have := ihV hVU hVw t htV (boundary_le V 0 true htV)
      have hE := hV.boundary k true
      have htE : t ∈ P.boundary (P.boundary V k true) 0 true := by
        rw [hgV 0 k hk0 true true]
        exact htV
      have hkn : k < n := by exact_mod_cast (lt_min_iff.1 hk).1.trans_le hVU
      have := ihn k hkn _ hE (krullDim_boundary_le V k true)
        (fun y hy => hVw y (boundary_le V k true hy)) t htE (boundary_le _ 0 true htE)
      have hinter : (P.boundary V k true : Set P) = (V : Set P) ∩ W := by
        rw [← LowerSet.coe_inf, hpaste.inf_eq_output]
      have := weakEquivalence_coneBase_congr R (w := w) hinter (boundary_le _ 0 true htE)
      have := weakEquivalence_coneBase_union R (w := w)
        (boundary_le V 0 true htV) (boundary_le W 0 true htW)
        hwV hwW mem_or_mem_of_le_or_le
      exact weakEquivalence_coneBase_congr R hUVW
        (Or.inl (boundary_le V 0 true htV))

end Molecule

section Horn

variable {C : Type} [PartialOrder C] (R : C → C → Prop) {Q : Set C} {x top t : C}

open scoped Classical in
theorem weakEquivalence_markedSubcomplexMap_chainSubcomplex_horn (htop : ∀ a, a ≤ top)
    (hQ : ∀ a, a ∈ Q ↔ a ≠ x ∧ a ≠ top) (hx : ∀ b, x ≤ b → b = x ∨ b = top)
    (hxtop : x ≠ top) (htQ : t ∈ Q) (hRt : R t top)
    (hRQ : ∀ a ∈ Q, R a top → ∃ c ∈ Q, t ≤ c ∧ (R t c ∨ t = c) ∧ R c top ∧ a ≤ c ∧
      (R a c ∨ a = c)) (hRx : R x top)
    (hRx' : ∀ a, a ≤ x → R a x → R a top)
    [WeakEquivalence (markedSubcomplexMap (edgeSet.{u} fun a b => R a b ∧ b ≠ top)
      (coneBase_le (Λ := Q) (w := top) htQ))] :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (chainSubcomplex_mono (Set.subset_univ Q))) := by
  have htopQ : top ∉ Q := fun h => ((hQ top).1 h).2 rfl
  have htt : t ≠ top := fun h => htopQ (h ▸ htQ)
  let Rm : C → C → Prop := fun a b => R a b ∧ b ≠ top
  let Rp : C → C → Prop := fun a b => Rm a b ∨ (a = t ∧ b = top)
  have hRmp : ∀ a b, Rm a b → Rp a b := fun _ _ h => Or.inl h
  have hRpR : ∀ a b, Rp a b → R a b := by
    rintro a b (h | ⟨rfl, rfl⟩)
    · exact h.1
    · exact hRt
  have h₁ : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} Rp)
      (coneBase_le (Λ := Q) (w := top) htQ)) := by
    refine weakEquivalence_markedSubcomplexMap_of_subset (edgeSet_mono hRmp) _ fun e he => ?_
    rcases he with he | ⟨h₀, h₁⟩
    · exact Or.inl he
    · refine Or.inr (Or.inr fun j => ?_)
      fin_cases j
      · exact Or.inl h₀
      · exact Or.inr h₁
  have sq : (chainSubcomplex.{u} ({t} : Set C)).BicartSq (chainSubcomplex Q)
      (chainSubcomplex {t, top}) (coneBase Q t top) := by
    refine ⟨rfl, ?_⟩
    rw [← chainSubcomplex_inter]
    congr 1
    ext a
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha, rfl | rfl⟩
      · rfl
      · exact absurd ha htopQ
    · rintro rfl
      exact ⟨htQ, Or.inl rfl⟩
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} Rp) sq.le₁₃) :=
    weakEquivalence_chainSubcomplex_collapse Rp (u := top) (T' := {t, top})
      (fun a => ⟨fun h => ⟨Or.inl h, fun hat => htt (h ▸ hat)⟩,
        fun ⟨h, hat⟩ => h.resolve_right hat⟩)
      (Or.inl rfl) htt (htop t) (Or.inr ⟨rfl, rfl⟩)
      (fun a ha hat _ => by
        obtain rfl := ha.resolve_right hat
        exact ⟨le_refl _, fun _ => Or.inr rfl⟩)
      (fun a ha hat _ => by
        obtain rfl := ha.resolve_right hat
        exact ⟨le_refl _, fun _ => Or.inr rfl⟩)
  have h₂ := weakEquivalence_markedSubcomplexMap_of_bicartSq (edgeSet Rp) sq
  let R₁ : C → C → Prop := fun a b => Rp a b ∨
    (b = top ∧ a ∈ Q ∧ t ≤ a ∧ (R t a ∨ t = a) ∧ R a top)
  have hRp₁ : ∀ a b, Rp a b → R₁ a b := fun _ _ h => Or.inl h
  have hR₁R : ∀ a b, R₁ a b → R a b := by
    rintro a b (h | ⟨rfl, -, -, -, h⟩)
    · exact hRpR a b h
    · exact h
  have h₃ : WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hRp₁)
      (chainSubcomplex.{u} (insert top Q))) := by
    refine weakEquivalence_markedSubcomplexRemark_chainSubcomplex hRp₁ _
      fun a _ b _ _ h => ?_
    rcases h with h | ⟨rfl, haQ, hta, hRta, -⟩
    · exact Or.inl h
    · refine Or.inr ⟨t, Set.mem_insert_of_mem _ htQ, Or.inl ⟨hta, ?_, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩⟩
      rcases hRta with hRta | hRta
      · exact Or.inl (Or.inl ⟨hRta, fun hat => htopQ (hat ▸ haQ)⟩)
      · exact Or.inr hRta
  have h₃' : WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hR₁R)
      (chainSubcomplex.{u} (insert top Q))) := by
    refine weakEquivalence_markedSubcomplexRemark_chainSubcomplex hR₁R _
      fun a ha b hb hab h => ?_
    by_cases hbt : b = top
    · by_cases hat : a = top
      · exact Or.inr ⟨a, ha, Or.inl ⟨le_refl _, Or.inr rfl, Or.inr (hat.trans hbt.symm)⟩⟩
      · have haQ : a ∈ Q := (Set.mem_insert_iff.1 ha).resolve_left hat
        obtain ⟨c, hcQ, htc, hRtc, hRct, hac, hRac⟩ := hRQ a haQ (hbt ▸ h)
        refine Or.inr ⟨c, Set.mem_insert_of_mem _ hcQ, Or.inr (Or.inl ⟨hac, hbt ▸ htop c, ?_,
          Or.inl (Or.inr ⟨hbt, hcQ, htc, hRtc, hRct⟩)⟩)⟩
        rcases hRac with hRac | hRac
        · exact Or.inl (Or.inl (Or.inl ⟨hRac, fun hct => htopQ (hct ▸ hcQ)⟩))
        · exact Or.inr hRac
    · exact Or.inl (Or.inl (Or.inl ⟨h, hbt⟩))
  have h₄ : WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hRpR) (chainSubcomplex.{u} Q)) :=
    weakEquivalence_markedSubcomplexRemark_chainSubcomplex hRpR _
      fun a _ b hb _ h => Or.inl (Or.inl ⟨h, fun hbt => htopQ (hbt ▸ hb)⟩)
  have h₅ : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (chainSubcomplex_mono (Set.subset_univ (insert top Q)))) := by
    refine weakEquivalence_markedSubcomplexMap_chainSubcomplex_of_retraction R
      (fun a => if a = x then top else a) false (Set.subset_univ _)
      (fun a _ b _ hab => ?_) (fun a _ => ?_)
      (fun a ha => ?_) (fun a _ => ?_) (fun a _ b _ hab h => ?_)
    · by_cases hax : a = x <;> by_cases hbx : b = x
      · simp only [hax, hbx, ↓reduceIte, le_refl]
      · simp only [hax, hbx, ↓reduceIte]
        rcases hx b (hax ▸ hab) with h | h
        · exact absurd h hbx
        · exact h.symm ▸ le_refl _
      · simp only [hax, hbx, ↓reduceIte]
        exact htop a
      · simp only [hax, hbx, ↓reduceIte]
        exact hab
    · by_cases hax : a = x
      · simp only [hax, ↓reduceIte]
        exact Set.mem_insert _ _
      · simp only [hax, ↓reduceIte]
        by_cases hat : a = top
        · exact hat ▸ Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ((hQ a).2 ⟨hax, hat⟩)
    · have hax : a ≠ x := by
        rintro rfl
        rcases Set.mem_insert_iff.1 ha with h | h
        · exact hxtop h
        · exact ((hQ a).1 h).1 rfl
      simp only [hax, ↓reduceIte]
    · by_cases hax : a = x
      · simp only [hax, ↓reduceIte, cond_false]
        exact htop x
      · simp only [hax, ↓reduceIte, cond_false, le_refl]
    · by_cases hax : a = x <;> by_cases hbx : b = x
      · subst hax
        subst hbx
        simp only [↓reduceIte, or_true, cond_false, true_and]
        exact Or.inl hRx
      · subst hax
        obtain rfl := (hx b hab).resolve_left hbx
        simp only [↓reduceIte, hbx, or_true, cond_false, true_and]
        exact Or.inl hRx
      · subst hbx
        simp only [hax, ↓reduceIte, cond_false]
        rcases h with h | h
        · exact ⟨Or.inl (hRx' a hab h), Or.inl (hRx' a hab h)⟩
        · exact absurd h hax
      · simp only [hax, hbx, ↓reduceIte, cond_false, and_self]
        exact h
  have e : markedSubcomplexRemark (edgeSet_mono hRpR) (chainSubcomplex.{u} Q) ≫
      markedSubcomplexMap (edgeSet R) (chainSubcomplex_mono (Set.subset_univ Q)) =
      markedSubcomplexMap (edgeSet Rp) sq.le₂₄ ≫
        markedSubcomplexMap (edgeSet Rp) (coneBase_le (Λ := Q) (w := top) htQ) ≫
          markedSubcomplexRemark (edgeSet_mono hRp₁) (chainSubcomplex (insert top Q)) ≫
            markedSubcomplexRemark (edgeSet_mono hR₁R) (chainSubcomplex (insert top Q)) ≫
              markedSubcomplexMap (edgeSet R)
                (chainSubcomplex_mono (Set.subset_univ (insert top Q))) :=
    MarkedPresheaf.hom_ext rfl
  have : WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hRpR) (chainSubcomplex.{u} Q) ≫
      markedSubcomplexMap (edgeSet R) (chainSubcomplex_mono (Set.subset_univ Q))) := by
    rw [e]
    infer_instance
  exact weakEquivalence_of_precomp (markedSubcomplexRemark (edgeSet_mono hRpR) (chainSubcomplex Q))
    _

theorem weakEquivalence_markedSubcomplexMap_chainSubcomplex_horn_of_le {R' : C → C → Prop}
    (hRR' : ∀ a b, R a b → R' a b) (hR'R : ∀ a b, R' a b → b ≠ top → R a b)
    (htop : ∀ a, a ≤ top) (hQ : ∀ a, a ∈ Q ↔ a ≠ x ∧ a ≠ top)
    (hx : ∀ b, x ≤ b → b = x ∨ b = top) (hxtop : x ≠ top) (htQ : t ∈ Q) (hRt : R' t top)
    (hRQ : ∀ a ∈ Q, R' a top → ∃ c ∈ Q, t ≤ c ∧ (R' t c ∨ t = c) ∧ R' c top ∧ a ≤ c ∧
      (R' a c ∨ a = c)) (hRx : R' x top)
    (hRx' : ∀ a, a ≤ x → R' a x → R' a top)
    [WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hRR')
      (chainSubcomplex.{u} (Set.univ : Set C)))]
    [WeakEquivalence (markedSubcomplexMap (edgeSet.{u} fun a b => R a b ∧ b ≠ top)
      (coneBase_le (Λ := Q) (w := top) htQ))] :
    WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (chainSubcomplex_mono (Set.subset_univ Q))) := by
  have htopQ : top ∉ Q := fun h => ((hQ top).1 h).2 rfl
  have he : (edgeSet.{u} fun a b => R' a b ∧ b ≠ top) = edgeSet fun a b => R a b ∧ b ≠ top :=
    Set.ext fun _ => ⟨fun h => ⟨hR'R _ _ h.1 h.2, h.2⟩, fun h => ⟨hRR' _ _ h.1, h.2⟩⟩
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} fun a b => R' a b ∧ b ≠ top)
      (coneBase_le (Λ := Q) (w := top) htQ)) := by
    rw [he]
    infer_instance
  have := weakEquivalence_markedSubcomplexMap_chainSubcomplex_horn R' htop hQ hx hxtop htQ hRt hRQ
    hRx hRx'
  have : WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hRR') (chainSubcomplex.{u} Q)) :=
    weakEquivalence_markedSubcomplexRemark_chainSubcomplex hRR' _
      fun _ _ b hb _ h => Or.inl (hR'R _ _ h fun hbt => htopQ (hbt ▸ hb))
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (chainSubcomplex_mono
      (Set.subset_univ Q)) ≫ markedSubcomplexRemark (edgeSet_mono hRR')
        (chainSubcomplex (Set.univ : Set C))) := by
    rw [markedSubcomplexMap_comp_markedSubcomplexRemark]
    infer_instance
  exact weakEquivalence_of_postcomp _ (markedSubcomplexRemark (edgeSet_mono hRR')
    (chainSubcomplex (Set.univ : Set C)))

end Horn

end Atoms.Diagrammatic
