import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.OpenBox
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialNerve

universe w v u

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory EnrichedCategory
  SimplicialCategory

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [SimplicialCategory C] {m : SimplexCategoryᵒᵖ}

private lemma eComp_eId_app {X Y : C} (w : (X ⟶[SSet] Y).obj m) :
    (eComp SSet X X Y).app m ((eId SSet X).app m PUnit.unit, w) = w :=
  congrArg (fun φ ↦ φ.app m w) (e_id_comp SSet X Y)

private lemma eComp_eId_app' {X Y : C} (w : (X ⟶[SSet] Y).obj m) :
    (eComp SSet X Y Y).app m (w, (eId SSet Y).app m PUnit.unit) = w :=
  congrArg (fun φ ↦ φ.app m w) (e_comp_id SSet X Y)

private lemma eComp_assoc_app {W X Y Z : C} (p : (W ⟶[SSet] X).obj m) (q : (X ⟶[SSet] Y).obj m)
    (r : (Y ⟶[SSet] Z).obj m) : (eComp SSet W Y Z).app m ((eComp SSet W X Y).app m (p, q), r) =
      (eComp SSet W X Z).app m (p, (eComp SSet X Y Z).app m (q, r)) :=
  congrArg (fun φ ↦ φ.app m ((p, q), r)) (e_assoc' SSet W X Y Z).symm

variable {D : Type*} [Category D] [SimplicialCategory D] (F : EnrichedFunctor SSet D C)

private lemma map_comp_app {a b c : D} {X Y Z : C} (ha : F.obj a = X) (hb : F.obj b = Y)
    (hc : F.obj c = Z) (p : (a ⟶[SSet] b).obj m) (q : (b ⟶[SSet] c).obj m) :
    (F.map a c ≫ eqToHom (by rw [ha, hc])).app m ((eComp SSet a b c).app m (p, q)) =
      (eComp SSet X Y Z).app m ((F.map a b ≫ eqToHom (by rw [ha, hb])).app m p,
        (F.map b c ≫ eqToHom (by rw [hb, hc])).app m q) := by
  subst ha hb hc
  simp only [eqToHom_refl, Category.comp_id]
  exact congrArg (fun φ ↦ φ.app m (p, q)) (F.map_comp a b c)

private lemma map_id_app {a : D} {X : C} (ha : F.obj a = X) :
    (F.map a a ≫ eqToHom (by rw [ha])).app m ((eId SSet a).app m PUnit.unit) =
      (eId SSet X).app m PUnit.unit := by
  subst ha
  simp only [eqToHom_refl, Category.comp_id]
  exact congrArg (fun φ ↦ φ.app m PUnit.unit) (F.map_id a)

private lemma map_eqToHom_congr {F F' : EnrichedFunctor SSet D C} (e : F = F') {a b : D}
    {Z : SSet.{v}} (h : (F.obj a ⟶[SSet] F.obj b) = Z) (h' : (F'.obj a ⟶[SSet] F'.obj b) = Z) :
    F.map a b ≫ eqToHom h = F'.map a b ≫ eqToHom h' := by subst e; rfl

end

namespace SimplicialThickening

variable {J : Type v} [LinearOrder J]

instance (a b : J) : Quiver.IsThin (Path a b) := fun _ _ ↦ ⟨fun f g ↦ by
  cases f; cases g; congr; subsingleton⟩

instance (a b : SimplicialThickening J) : Quiver.IsThin (a ⟶ b) :=
  inferInstanceAs (Quiver.IsThin (Path a.as b.as))

instance (a : SimplicialThickening J) : Subsingleton (a ⟶ a) :=
  ⟨fun f g ↦ by
    ext t
    have hf := fun h ↦ le_antisymm (f.le_right t h) (f.left_le t h)
    have hg := fun h ↦ le_antisymm (g.le_right t h) (g.left_le t h)
    exact ⟨fun h ↦ hf h ▸ g.left, fun h ↦ hg h ▸ f.left⟩⟩

instance isIso_eHomEquiv {a b : SimplicialThickening J} [Subsingleton (a ⟶ b)] (f : a ⟶ b) :
    IsIso (eHomEquiv SSet f) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun n ↦ ?_
  rw [isIso_iff_bijective]
  exact ⟨fun _ _ _ ↦ rfl, fun _ ↦ ⟨PUnit.unit,
    nerve.ext_of_isThin (funext fun _ ↦ Subsingleton.elim _ _)⟩⟩

def isInitialHom {a b : SimplicialThickening J} (h : ¬ a.as ≤ b.as) :
    Limits.IsInitial (a ⟶[SSet] b) :=
  Limits.IsInitial.ofUniqueHom
    (fun _ ↦ { app _ := ↾fun z ↦ absurd (Path.le (z.obj 0)) h
               naturality _ _ _ := by ext z; exact absurd (Path.le (z.obj 0)) h })
    (fun _ _ ↦ by ext _ z; exact absurd (Path.le (z.obj 0)) h)

lemma map_eq_toUnit_comp {C : Type u} [Category.{v} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet (SimplicialThickening J) C) {a b : SimplicialThickening J}
    [Subsingleton (a ⟶ b)] (f : a ⟶ b) :
    F.map a b = toUnit _ ≫ eHomEquiv SSet f ≫ F.map a b := by
  rw [← Category.assoc, ← cancel_epi (eHomEquiv SSet f), ← Category.assoc]
  congr 1

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

@[implicit_reducible, simps obj]
noncomputable def ofFunctor (F : J ⥤ C) : EnrichedFunctor SSet (SimplicialThickening J) C where
  obj a := F.obj a.as
  map a b := if h : a.as ≤ b.as then toUnit _ ≫ eHomEquiv SSet (F.map (homOfLE h))
    else (isInitialHom h).to _
  map_id a := by
    rw [dif_pos le_rfl]
    simp only [homOfLE_refl, F.map_id, eHomEquiv_id]
    rw [← Category.assoc, toUnit_unique (eId SSet a ≫ toUnit _) (𝟙 _), Category.id_comp]
  map_comp a b c := by
    by_cases hab : a.as ≤ b.as
    · by_cases hbc : b.as ≤ c.as
      · rw [dif_pos hab, dif_pos hbc, dif_pos (hab.trans hbc), ← homOfLE_comp hab hbc,
          F.map_comp, eHomEquiv_comp, ← tensorHom_comp_tensorHom_assoc]
        simp only [← Category.assoc]
        congr 2
      · ext n z
        exact absurd (Path.le (z.2.obj 0)) hbc
    · ext n z
      exact absurd (Path.le (z.1.obj 0)) hab

lemma ofFunctor_map_of_le (F : J ⥤ C) {a b : SimplicialThickening J} (h : a.as ≤ b.as) :
    (ofFunctor F).map a b = toUnit _ ≫ eHomEquiv SSet (F.map (homOfLE h)) :=
  dif_pos h

lemma eq_ofFunctor_const [Subsingleton J] (F : EnrichedFunctor SSet (SimplicialThickening J) C)
    (a₀ : J) : F = ofFunctor ((Functor.const J).obj (F.obj ⟨a₀⟩)) := by
  have h (a : SimplicialThickening J) : a = ⟨a₀⟩ := by
    rcases a with ⟨a⟩
    rw [Subsingleton.elim a a₀]
  refine EnrichedFunctor.ext _ (fun a ↦ by rw [h a]; rfl) (fun a b ↦ ?_)
  obtain rfl := h a
  obtain rfl := h b
  rw [ofFunctor_map_of_le _ le_rfl, map_eq_toUnit_comp F (𝟙 _), eHomEquiv_id, F.map_id]
  simp only [Functor.const_obj_obj, Functor.const_obj_map, eHomEquiv_id]
  exact Category.comp_id _

variable {a b : SimplicialThickening J} {m : SimplexCategoryᵒᵖ}

private lemma simplex_ext {z w : (a ⟶[SSet] b).obj m} (h : ∀ t, (z.obj t).I = (w.obj t).I) :
    z = w :=
  nerve.ext_of_isThin (funext fun t ↦ Path.ext (h t))

private def restrict (c d : SimplicialThickening J) (h : c.as ≤ d.as) : (a ⟶ b) ⥤ (c ⟶ d) where
  obj I :=
    { I := I.I ∩ Set.Icc c.as d.as ∪ {c.as, d.as}
      left := Or.inr (Or.inl rfl)
      right := Or.inr (Or.inr rfl)
      left_le := by grind
      le_right := by grind }
  map f := InducedCategory.homMk (homOfLE
    (Set.union_subset_union_left _ (Set.inter_subset_inter_left _ f.hom.le)))

private lemma eComp_restrict (x y w : SimplicialThickening J) (hxy : x.as ≤ y.as)
    (hyw : y.as ≤ w.as) (z : (a ⟶[SSet] b).obj m) (hy : ∀ t, y.as ∈ (z.obj t).I) :
    (eComp SSet x y w).app m ((nerveMap (restrict x y hxy)).app m z,
      (nerveMap (restrict y w hyw)).app m z) = (nerveMap (restrict x w (hxy.trans hyw))).app m z :=
  simplex_ext fun t ↦ Set.ext fun s ↦ by
    change s ∈ (_ ∩ _ ∪ {x.as, y.as}) ∪ (_ ∩ _ ∪ {y.as, w.as}) ↔
      s ∈ (z.obj t).I ∩ Set.Icc x.as w.as ∪ _
    grind [hy t]

private lemma restrict_self (h : a.as ≤ b.as) (z : (a ⟶[SSet] b).obj m) :
    (nerveMap (restrict a b h)).app m z = z :=
  simplex_ext fun t ↦ Set.ext fun s ↦ by
    change s ∈ (z.obj t).I ∩ Set.Icc a.as b.as ∪ {a.as, b.as} ↔ _
    grind [Path.left, Path.right, Path.left_le, Path.le_right]

private lemma restrict_eComp {c : SimplicialThickening J} (hab : a.as ≤ b.as) (hbc : b.as ≤ c.as)
    (p : (a ⟶[SSet] b).obj m) (q : (b ⟶[SSet] c).obj m) :
    (nerveMap (restrict a b hab)).app m ((eComp SSet a b c).app m (p, q)) = p ∧
      (nerveMap (restrict b c hbc)).app m ((eComp SSet a b c).app m (p, q)) = q := by
  refine ⟨simplex_ext fun t ↦ Set.ext fun s ↦ ?_, simplex_ext fun t ↦ Set.ext fun s ↦ ?_⟩ <;>
  · change s ∈ ((p.obj t).I ∪ (q.obj t).I) ∩ Set.Icc _ _ ∪ {_, _} ↔ _
    have := (p.obj t).left_le s
    have := (p.obj t).le_right s
    have := (q.obj t).left_le s
    have := (q.obj t).le_right s
    grind [Path.left, Path.right]

end SimplicialThickening

namespace SimplicialNerve

open SimplicialThickening

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

noncomputable def objEquiv (C : Type u) [Category.{v} C] [SimplicialCategory C] :
    (SimplicialNerve C) _⦋0⦌ ≃ C where
  toFun F := F.obj ⟨⟨0⟩⟩
  invFun x := ofFunctor ((Functor.const _).obj x)
  left_inv F := (eq_ofFunctor_const (J := ULift.{v} (Fin 1)) F ⟨0⟩).symm
  right_inv _ := rfl

@[simp]
lemma objEquiv_apply (F : (SimplicialNerve C) _⦋0⦌) : objEquiv C F = F.obj ⟨⟨0⟩⟩ := rfl

private lemma fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

private def path01 : (⟨⟨0⟩⟩ : SimplicialThickening (ULift.{v} (Fin 2))) ⟶ ⟨⟨1⟩⟩ where
  I := Set.univ
  left := trivial
  right := trivial
  left_le k _ := Fin.zero_le k.down
  le_right k _ := Fin.le_last k.down

instance : Subsingleton ((⟨⟨0⟩⟩ : SimplicialThickening (ULift.{v} (Fin 2))) ⟶ ⟨⟨1⟩⟩) :=
  ⟨fun f g ↦ by
    ext ⟨t⟩
    fin_cases t
    · exact iff_of_true f.left g.left
    · exact iff_of_true f.right g.right⟩

private noncomputable def edgeHom
    (e : EnrichedFunctor SSet (SimplicialThickening (ULift.{v} (Fin 2))) C) :
    e.obj ⟨⟨0⟩⟩ ⟶ e.obj ⟨⟨1⟩⟩ :=
  (eHomEquiv SSet).symm (eHomEquiv SSet path01 ≫ e.map _ _)

private lemma monotone_down : Monotone (ULift.down : ULift.{v} (Fin 2) → Fin 2) := fun _ _ h ↦ h

private lemma eq_ofFunctor_edgeHom
    (e : EnrichedFunctor SSet (SimplicialThickening (ULift.{v} (Fin 2))) C) :
    e = ofFunctor (monotone_down.functor ⋙ ComposableArrows.mk₁ (edgeHom e)) := by
  refine EnrichedFunctor.ext _ (fun ⟨⟨a⟩⟩ ↦ by obtain rfl | rfl := fin_two_cases a <;> rfl)
    (fun ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ↦ ?_)
  obtain rfl | rfl := fin_two_cases a <;> obtain rfl | rfl := fin_two_cases b
  · rw [map_eq_toUnit_comp e (𝟙 _), eHomEquiv_id, e.map_id, ofFunctor_map_of_le _ le_rfl]
    simp only [homOfLE_refl, Functor.map_id, eHomEquiv_id]
    exact Category.comp_id _
  · refine (Category.comp_id _).trans ((map_eq_toUnit_comp e path01).trans
      (Eq.trans ?_ (ofFunctor_map_of_le (monotone_down.functor ⋙ ComposableArrows.mk₁ (edgeHom e))
        (a := ⟨⟨0⟩⟩) (b := ⟨⟨1⟩⟩) (Fin.zero_le _)).symm))
    congr 1
    exact ((eHomEquiv SSet).apply_symm_apply _).symm
  · exact (isInitialHom (by decide)).hom_ext _ _
  · rw [map_eq_toUnit_comp e (𝟙 _), eHomEquiv_id, e.map_id, ofFunctor_map_of_le _ le_rfl]
    simp only [homOfLE_refl, Functor.map_id, eHomEquiv_id]
    exact Category.comp_id _

private lemma edgeHom_ofFunctor (φ : ULift.{v} (Fin 2) ⥤ C) :
    edgeHom (ofFunctor φ) = φ.map (homOfLE (Fin.zero_le 1)) := by
  rw [edgeHom, ofFunctor_map_of_le φ (a := ⟨⟨0⟩⟩) (b := ⟨⟨1⟩⟩) (Fin.zero_le _), ← Category.assoc,
    toUnit_unique (_ ≫ toUnit _) (𝟙 _), Category.id_comp, Equiv.symm_apply_apply]

noncomputable def edgeEquiv (x y : C) :
    {e : (SimplicialNerve C) _⦋1⦌ //
      objEquiv C ((SimplicialNerve C).δ 1 e) = x ∧ objEquiv C ((SimplicialNerve C).δ 0 e) = y} ≃
      (x ⟶ y) where
  toFun e := eqToHom e.2.1.symm ≫ edgeHom e.1 ≫ eqToHom e.2.2
  invFun f := ⟨ofFunctor (monotone_down.functor ⋙ ComposableArrows.mk₁ f), rfl, rfl⟩
  left_inv := by
    rintro ⟨e, rfl, rfl⟩
    refine Subtype.ext (Eq.trans ?_ (eq_ofFunctor_edgeHom e).symm)
    exact congrArg (fun g ↦ ofFunctor (monotone_down.functor ⋙ ComposableArrows.mk₁ g))
      ((Category.id_comp _).trans (Category.comp_id _))
  right_inv f :=
    (Category.id_comp _).trans ((Category.comp_id _).trans (edgeHom_ofFunctor _))

open SSet

private noncomputable def retraction {k : ℕ} (S : Set (Fin (k + 1))) (a : Fin (k + 1)) :
    ⦋k⦌ ⟶ ⦋k⦌ :=
  SimplexCategory.mkHom
    { toFun t := a ⊔ sSup {s ∈ S | s ≤ t}
      monotone' _ _ h := sup_le_sup_left (sSup_le_sSup fun _ hs ↦ And.intro hs.1 (hs.2.trans h))
        _ }

private lemma retraction_apply_of_mem {k : ℕ} {S : Set (Fin (k + 1))} {a s : Fin (k + 1)}
    (hs : s ∈ S) (has : a ≤ s) : (retraction S a).toOrderHom s = s :=
  (congrArg (a ⊔ ·) (le_antisymm (sSup_le fun _ ht ↦ ht.2) (le_sSup (And.intro hs le_rfl)))).trans
    (sup_eq_right.2 has)

private lemma retraction_apply_mem {k : ℕ} {S : Set (Fin (k + 1))} {a : Fin (k + 1)} (ha : a ∈ S)
    (t : Fin (k + 1)) : (retraction S a).toOrderHom t ∈ S := by
  change a ⊔ sSup {s ∈ S | s ≤ t} ∈ S
  rcases Set.eq_empty_or_nonempty {s ∈ S | s ≤ t} with h | h
  · rwa [h, sSup_empty, sup_eq_left.2 bot_le]
  · exact sup_ind (p := (· ∈ S)) a _ ha (h.csSup_mem (Set.toFinite _)).1

variable {m : SimplexCategoryᵒᵖ}

section Horn

variable {n : ℕ} {i : Fin (n + 3)} (σ₀ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)

private def InHorn (i : Fin (n + 3)) {k : ℕ} (f : ⦋k⦌ ⟶ ⦋n + 2⦌) : Prop :=
  ∃ t, t ≠ i ∧ t ∉ Set.range f.toOrderHom

private lemma InHorn.mem {k : ℕ} {f : ⦋k⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i f) :
    stdSimplex.objEquiv.{w}.symm f ∈ (Λ[n + 2, i] : (Δ[n + 2] : SSet.{w}).Subcomplex).obj _ :=
  (mem_horn_iff_notMem_range _ _).2 (let ⟨t, ht, ht'⟩ := hf; ⟨t, ht, ht'⟩)

private lemma InHorn.comp {k l : ℕ} {f : ⦋k⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i f) (g : ⦋l⦌ ⟶ ⦋k⦌) :
    InHorn i (g ≫ f) :=
  let ⟨t, ht, ht'⟩ := hf
  ⟨t, ht, fun ⟨_, hs⟩ ↦ ht' ⟨_, hs⟩⟩

private lemma inHorn_const (c : Fin (n + 3)) : InHorn i (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ c) :=
  let ⟨t, ht, htc⟩ := Fin.exists_ne_and_ne_of_two_lt i c (by lia)
  ⟨t, ht, fun ⟨_, h⟩ ↦ htc h.symm⟩

private def hornVal {k : ℕ} (f : ⦋k⦌ ⟶ ⦋n + 2⦌) (hf : InHorn i f) :
    EnrichedFunctor SSet (SimplicialThickening (ULift.{v} (Fin (k + 1)))) C :=
  σ₀.app _ ⟨_, hf.mem⟩

private lemma hornVal_congr {k : ℕ} {f f' : ⦋k⦌ ⟶ ⦋n + 2⦌} (h : f = f') (hf : InHorn i f)
    (hf' : InHorn i f') : hornVal σ₀ f hf = hornVal σ₀ f' hf' := by subst h; rfl

private lemma hornVal_comp {k l : ℕ} (g : ⦋l⦌ ⟶ ⦋k⦌) (f : ⦋k⦌ ⟶ ⦋n + 2⦌) (hf : InHorn i f) :
    hornVal σ₀ (g ≫ f) (hf.comp g) = (functor g.toOrderHom.uliftMap).comp SSet (hornVal σ₀ f hf) :=
  congrArg (fun φ ↦ φ ⟨_, hf.mem⟩) (σ₀.naturality g.op)

private def vert (c : Fin (n + 3)) : C :=
  (hornVal σ₀ (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ c) (inHorn_const c)).obj ⟨⟨0⟩⟩

private lemma hornVal_obj {k : ℕ} (f : ⦋k⦌ ⟶ ⦋n + 2⦌) (hf : InHorn i f)
    (a : SimplicialThickening (ULift.{v} (Fin (k + 1)))) :
    (hornVal σ₀ f hf).obj a = vert σ₀ (f.toOrderHom a.as.down) := by
  rw [vert, hornVal_congr σ₀ (SimplexCategory.const_comp _ f a.as.down).symm _ (hf.comp _),
    hornVal_comp]
  rfl

private def hornMap {k : ℕ} (f : ⦋k⦌ ⟶ ⦋n + 2⦌) (hf : InHorn i f)
    {a b : SimplicialThickening (ULift.{v} (Fin (k + 1)))} {a' b' : Fin (n + 3)}
    (ha : f.toOrderHom a.as.down = a') (hb : f.toOrderHom b.as.down = b') :
    (a ⟶[SSet] b) ⟶ (vert σ₀ a' ⟶[SSet] vert σ₀ b') :=
  (hornVal σ₀ f hf).map a b ≫ eqToHom (by rw [hornVal_obj, hornVal_obj, ha, hb])

variable {k : ℕ} {a b : SimplicialThickening (ULift.{v} (Fin (k + 1)))} {a' b' : Fin (n + 3)}

private lemma hornMap_comp {l : ℕ} (g : ⦋l⦌ ⟶ ⦋k⦌) (f : ⦋k⦌ ⟶ ⦋n + 2⦌) (hf : InHorn i f)
    {a b : SimplicialThickening (ULift.{v} (Fin (l + 1)))}
    (ha : (g ≫ f).toOrderHom a.as.down = a') (hb : (g ≫ f).toOrderHom b.as.down = b') :
    hornMap σ₀ (g ≫ f) (hf.comp g) ha hb =
      (functor g.toOrderHom.uliftMap).map a b ≫ hornMap σ₀ f hf ha hb :=
  (map_eqToHom_congr (hornVal_comp σ₀ g f hf) _ _).trans (Category.assoc _ _ _)

private lemma hornMap_app_congr {f : ⦋k⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i f)
    {a₂ b₂ : SimplicialThickening (ULift.{v} (Fin (k + 1)))}
    (ha : f.toOrderHom a.as.down = a') (hb : f.toOrderHom b.as.down = b')
    (ha₂ : f.toOrderHom a₂.as.down = a') (hb₂ : f.toOrderHom b₂.as.down = b')
    (e₁ : a = a₂) (e₂ : b = b₂) (z : (a ⟶[SSet] b).obj m) (w : (a₂ ⟶[SSet] b₂).obj m)
    (h : ∀ t, (z.obj t).I = (w.obj t).I) :
    (hornMap σ₀ f hf ha hb).app m z = (hornMap σ₀ f hf ha₂ hb₂).app m w := by
  subst e₁ e₂; rw [simplex_ext h]

private lemma hornMap_app_of_fix (ρ : ⦋k⦌ ⟶ ⦋k⦌) (f g : ⦋k⦌ ⟶ ⦋n + 2⦌) (e : ρ ≫ f = g)
    (hf : InHorn i f) (hg : InHorn i g)
    (ha : g.toOrderHom a.as.down = a') (hb : g.toOrderHom b.as.down = b')
    (ha' : f.toOrderHom a.as.down = a') (hb' : f.toOrderHom b.as.down = b')
    (z : (a ⟶[SSet] b).obj m) (hρ : ∀ t, ∀ s ∈ (z.obj t).I, ρ.toOrderHom s.down = s.down) :
    (hornMap σ₀ g hg ha hb).app m z = (hornMap σ₀ f hf ha' hb').app m z := by
  subst e
  rw [hornMap_comp, NatTrans.comp_app_apply]
  refine hornMap_app_congr σ₀ hf _ _ _ _ ?_ ?_ _ _ fun t ↦ Set.ext fun s ↦ ⟨?_, ?_⟩
  · exact congrArg SimplicialThickening.mk (ULift.ext _ _ (hρ 0 _ (z.obj 0).left))
  · exact congrArg SimplicialThickening.mk (ULift.ext _ _ (hρ 0 _ (z.obj 0).right))
  · rintro ⟨s, hs, rfl⟩
    rw [(ULift.ext _ _ (hρ t s hs) : ρ.toOrderHom.uliftMap s = s)]
    exact hs
  · exact fun hs ↦ ⟨s, hs, ULift.ext _ _ (hρ t s hs)⟩

private lemma hornMap_app_eq {f f' : ⦋k⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i f) (hf' : InHorn i f')
    (ha : f.toOrderHom a.as.down = a') (hb : f.toOrderHom b.as.down = b')
    (ha' : f'.toOrderHom a.as.down = a') (hb' : f'.toOrderHom b.as.down = b')
    (z : (a ⟶[SSet] b).obj m)
    (h : ∀ t, ∀ s ∈ (z.obj t).I, f.toOrderHom s.down = f'.toOrderHom s.down) :
    (hornMap σ₀ f hf ha hb).app m z = (hornMap σ₀ f' hf' ha' hb').app m z := by
  let S := {s | ∃ t, ULift.up s ∈ (z.obj t).I}
  have hρ : ∀ t, ∀ s ∈ (z.obj t).I, (retraction S a.as.down).toOrderHom s.down = s.down :=
    fun t s hs ↦ retraction_apply_of_mem ⟨t, hs⟩ ((z.obj t).left_le _ hs)
  have e : retraction S a.as.down ≫ f' = retraction S a.as.down ≫ f := by
    ext x : 3
    have haS : a.as.down ∈ S := ⟨0, (z.obj 0).left⟩
    obtain ⟨t, hs⟩ := retraction_apply_mem haS x
    exact (h t _ hs).symm
  have ha₀ := hρ 0 _ (z.obj 0).left
  have hb₀ := hρ 0 _ (z.obj 0).right
  exact (hornMap_app_of_fix σ₀ _ f _ rfl hf (hf.comp _) ((congrArg _ ha₀).trans ha)
    ((congrArg _ hb₀).trans hb) ha hb z hρ).symm.trans (hornMap_app_of_fix σ₀ _ f' _ e hf'
      (hf.comp _) ((congrArg _ ha₀).trans ha) ((congrArg _ hb₀).trans hb) ha' hb' z hρ)

private lemma hornMap_comp_app {c : SimplicialThickening (ULift.{v} (Fin (k + 1)))}
    {c' : Fin (n + 3)} {f : ⦋k⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i f) (ha : f.toOrderHom a.as.down = a')
    (hb : f.toOrderHom b.as.down = b') (hc : f.toOrderHom c.as.down = c')
    (p : (a ⟶[SSet] c).obj m) (q : (c ⟶[SSet] b).obj m) :
    (hornMap σ₀ f hf ha hb).app m ((eComp SSet a c b).app m (p, q)) =
      (eComp SSet _ _ _).app m ((hornMap σ₀ f hf ha hc).app m p, (hornMap σ₀ f hf hc hb).app m q) :=
  map_comp_app (hornVal σ₀ f hf) ((hornVal_obj _ _ _ _).trans (congrArg _ ha))
    ((hornVal_obj _ _ _ _).trans (congrArg _ hc)) ((hornVal_obj _ _ _ _).trans (congrArg _ hb)) p q

end Horn

section Filler

open Limits HomotopicalAlgebra modelCategoryQuillen

variable {n : ℕ} {i : Fin (n + 1)}
  (σ₀ : (Λ[n + 2, i.succ.castSucc] : SSet.{max u v}) ⟶ SimplicialNerve C)

private def clamp (c d : Fin (n + 3)) : ⦋n + 2⦌ ⟶ ⦋n + 2⦌ :=
  SimplexCategory.mkHom
    ⟨fun t ↦ max c (min t d), fun _ _ h ↦ max_le_max_left c (min_le_min_right d h)⟩

private lemma clamp_apply {c d s : Fin (n + 3)} (h₁ : c ≤ s) (h₂ : s ≤ d) :
    (clamp c d).toOrderHom s = s :=
  (congrArg (max c) (min_eq_left h₂)).trans (max_eq_right h₁)

private lemma inHorn_clamp {c d : Fin (n + 3)} (hcd : c ≤ d) (h : 0 < c ∨ d < Fin.last _) :
    InHorn i.succ.castSucc (clamp c d) := by
  rcases h with h | h
  · refine ⟨0, fun h' ↦ ?_, fun ⟨t, ht⟩ ↦ h.not_ge ((le_max_left c (min t d)).trans_eq ht)⟩
    simpa using congrArg Fin.val h'
  · exact ⟨Fin.last _, (Fin.castSucc_lt_last _).ne',
      fun ⟨t, ht⟩ ↦ h.not_ge (ht.symm.trans_le (max_le hcd (min_le_right t d)))⟩

variable {a b : SimplicialThickening (ULift.{v} (Fin (n + 3)))}

private abbrev clampMap (hab : a.as.down ≤ b.as.down) (h : 0 < a.as.down ∨ b.as.down < Fin.last _) :
    (a ⟶[SSet] b) ⟶ (vert σ₀ a.as.down ⟶[SSet] vert σ₀ b.as.down) :=
  hornMap σ₀ (clamp a.as.down b.as.down) (inHorn_clamp hab h) (clamp_apply le_rfl hab)
    (clamp_apply hab le_rfl)

private lemma fix_clamp (z : (a ⟶[SSet] b).obj m) {c d : Fin (n + 3)} (hc : c ≤ a.as.down)
    (hd : b.as.down ≤ d) : ∀ t, ∀ s ∈ (z.obj t).I, (clamp c d).toOrderHom s.down = s.down :=
  fun t s hs ↦ clamp_apply (hc.trans ((z.obj t).left_le s hs)) (((z.obj t).le_right s hs).trans hd)

private lemma clampMap_eId_app (h : 0 < a.as.down ∨ a.as.down < Fin.last _) :
    (clampMap σ₀ (b := a) le_rfl h).app m ((eId SSet a).app m PUnit.unit) =
      (eId SSet (vert σ₀ a.as.down)).app m PUnit.unit :=
  map_id_app (hornVal σ₀ (clamp a.as.down a.as.down) (inHorn_clamp le_rfl h))
    ((hornVal_obj σ₀ _ _ a).trans (congrArg (vert σ₀) (clamp_apply le_rfl le_rfl)))

private lemma hornMap_app_eq_clampMap {f : ⦋n + 2⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i.succ.castSucc f)
    (ha : f.toOrderHom a.as.down = a.as.down) (hb : f.toOrderHom b.as.down = b.as.down)
    (hab : a.as.down ≤ b.as.down) (h : 0 < a.as.down ∨ b.as.down < Fin.last _)
    (z : (a ⟶[SSet] b).obj m) (hfix : ∀ t, ∀ s ∈ (z.obj t).I, f.toOrderHom s.down = s.down) :
    (hornMap σ₀ f hf ha hb).app m z = (clampMap σ₀ hab h).app m z :=
  hornMap_app_eq σ₀ hf _ ha hb _ _ z fun t s hs ↦
    (hfix t s hs).trans (fix_clamp z le_rfl le_rfl t s hs).symm

private noncomputable def boxComp (c : Fin (n + 3)) (hac : a.as.down ≤ c) (hcb : c ≤ b.as.down)
    (h₀ : 0 < c) (hN : c < Fin.last _) :
    (a ⟶[SSet] b) ⟶ (vert σ₀ a.as.down ⟶[SSet] vert σ₀ b.as.down) :=
  lift (nerveMap (restrict a ⟨⟨c⟩⟩ hac)) (nerveMap (restrict ⟨⟨c⟩⟩ b hcb)) ≫
    (clampMap σ₀ (b := ⟨⟨c⟩⟩) hac (Or.inr hN) ⊗ₘ clampMap σ₀ (a := ⟨⟨c⟩⟩) hcb (Or.inl h₀)) ≫
      eComp SSet _ _ _

private lemma boxComp_app (c : Fin (n + 3)) (hac : a.as.down ≤ c) (hcb : c ≤ b.as.down)
    (h₀ : 0 < c) (hN : c < Fin.last _) (z : (a ⟶[SSet] b).obj m) :
    (boxComp σ₀ c hac hcb h₀ hN).app m z = (eComp SSet _ _ _).app m
      ((clampMap σ₀ (b := ⟨⟨c⟩⟩) hac (Or.inr hN)).app m ((nerveMap (restrict a _ hac)).app m z),
        (clampMap σ₀ (a := ⟨⟨c⟩⟩) hcb (Or.inl h₀)).app m ((nerveMap (restrict _ b hcb)).app m z)) :=
  rfl

private lemma hornMap_app_eq_boxComp {f : ⦋n + 2⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i.succ.castSucc f)
    (ha : f.toOrderHom a.as.down = a.as.down) (hb : f.toOrderHom b.as.down = b.as.down)
    (z : (a ⟶[SSet] b).obj m) (hfix : ∀ t, ∀ s ∈ (z.obj t).I, f.toOrderHom s.down = s.down)
    {c : Fin (n + 3)} (hac : a.as.down ≤ c) (hcb : c ≤ b.as.down) (h₀ : 0 < c)
    (hN : c < Fin.last _) (hc : ∀ t, ⟨c⟩ ∈ (z.obj t).I) :
    (hornMap σ₀ f hf ha hb).app m z = (boxComp σ₀ c hac hcb h₀ hN).app m z := by
  have hz := eComp_restrict a ⟨⟨c⟩⟩ b hac hcb z hc
  rw [restrict_self] at hz
  refine (congrArg (fun w ↦ (hornMap σ₀ f hf ha hb).app m w) hz.symm).trans ?_
  rw [hornMap_comp_app σ₀ hf ha hb (c := ⟨⟨c⟩⟩) (hfix 0 _ (hc 0))]
  have fix {x y : SimplicialThickening _} (hxy : x.as ≤ y.as) (hx : ∀ t, x.as ∈ (z.obj t).I)
      (hy : ∀ t, y.as ∈ (z.obj t).I) t s
      (hs : s ∈ (((nerveMap (restrict x y hxy)).app m z).obj t).I) :
      f.toOrderHom s.down = s.down := by
    rcases hs with ⟨hs, -⟩ | rfl | rfl
    exacts [hfix t s hs, hfix t _ (hx t), hfix t _ (hy t)]
  exact congrArg₂ (fun p q ↦ (eComp SSet _ _ _).app m (p, q))
    (hornMap_app_eq_clampMap σ₀ hf _ _ hac (.inr hN) _ (fix _ (fun t ↦ (z.obj t).left) hc))
    (hornMap_app_eq_clampMap σ₀ hf _ _ hcb (.inl h₀) _ (fix _ hc fun t ↦ (z.obj t).right))

private lemma boxComp_app_eq (z : (a ⟶[SSet] b).obj m) {c c' : Fin (n + 3)} (hcc' : c ≤ c')
    (hac : a.as.down ≤ c) (hcb : c ≤ b.as.down) (h₀ : 0 < c) (hN : c < Fin.last _)
    (hac' : a.as.down ≤ c') (hc'b : c' ≤ b.as.down) (h₀' : 0 < c') (hN' : c' < Fin.last _)
    (hc : ∀ t, ⟨c⟩ ∈ (z.obj t).I) (hc' : ∀ t, ⟨c'⟩ ∈ (z.obj t).I) :
    (boxComp σ₀ c hac hcb h₀ hN).app m z = (boxComp σ₀ c' hac' hc'b h₀' hN').app m z := by
  rw [boxComp_app, boxComp_app, ← eComp_restrict (⟨⟨c⟩⟩ : SimplicialThickening _) ⟨⟨c'⟩⟩ b hcc'
    hc'b z hc', ← eComp_restrict a ⟨⟨c⟩⟩ ⟨⟨c'⟩⟩ hac hcc' z hc,
    hornMap_comp_app σ₀ _ _ _ (clamp_apply hcc' hc'b),
    hornMap_comp_app σ₀ _ _ _ (clamp_apply hac hcc'), eComp_assoc_app]
  refine congrArg₂ (fun p q ↦ (eComp SSet _ _ _).app m (p, q))
    (hornMap_app_eq_clampMap σ₀ _ _ _ _ _ _ (fix_clamp _ le_rfl hcc')).symm
    (congrArg₂ (fun p q ↦ (eComp SSet _ _ _).app m (p, q)) ?_
      (hornMap_app_eq_clampMap σ₀ _ _ _ _ _ _ (fix_clamp _ hcc' le_rfl)))
  exact hornMap_app_eq σ₀ _ _ _ _ _ _ _ fun t s hs ↦
    (fix_clamp _ le_rfl hc'b t s hs).trans (fix_clamp _ hac le_rfl t s hs).symm

private lemma vertex_cases (s : Fin (n + 3)) :
    s = 0 ∨ s = Fin.last _ ∨ ∃ k : Fin (n + 1), s = k.succ.castSucc := by
  induction s using Fin.lastCases with
  | last => exact Or.inr (Or.inl rfl)
  | cast s => induction s using Fin.cases with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr (Or.inr ⟨k, rfl⟩)

variable (n) in
open Classical in
noncomputable def cubeFun :
    ((⟨⟨0⟩⟩ : SimplicialThickening (ULift.{v} (Fin (n + 3)))) ⟶ ⟨⟨Fin.last _⟩⟩) ⥤
      ULift.{v} (Fin (n + 1) → Fin 2) where
  obj I := ⟨fun k ↦ if ⟨k.succ.castSucc⟩ ∈ I.I then 1 else 0⟩
  map f := homOfLE fun k ↦ by
    dsimp only
    split_ifs with h h'
    exacts [le_rfl, absurd (f.hom.le h) h', Fin.zero_le _, le_rfl]

variable (n) in
private def cubeInv : ULift.{v} (Fin (n + 1) → Fin 2) ⥤
    ((⟨⟨0⟩⟩ : SimplicialThickening (ULift.{v} (Fin (n + 3)))) ⟶ ⟨⟨Fin.last _⟩⟩) where
  obj g :=
    { I := {s | s.down = 0 ∨ s.down = Fin.last _ ∨ ∃ k, s.down = k.succ.castSucc ∧ g.down k ≠ 0}
      left := Or.inl rfl
      right := Or.inr (Or.inl rfl)
      left_le _ _ := Fin.zero_le _
      le_right _ _ := Fin.le_last _ }
  map f := InducedCategory.homMk (homOfLE fun _ ↦ Or.imp_right (Or.imp_right
    fun ⟨k, hk, hg⟩ ↦ ⟨k, hk, fun h ↦ hg (le_antisymm (h ▸ f.le k) (Fin.zero_le _))⟩))

open Classical in
instance : IsIso (nerveMap.{v} (cubeFun n)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun _ ↦ ?_
  rw [isIso_iff_bijective]
  refine ⟨fun z z' h ↦ nerve.ext_of_isThin (funext fun t ↦ Path.ext (Set.ext fun ⟨s⟩ ↦ ?_)),
    fun w ↦ ⟨w ⋙ cubeInv n, nerve.ext_of_isThin (funext fun t ↦ ULift.ext _ _ (funext fun k ↦ ?_))⟩⟩
  · rcases vertex_cases s with rfl | rfl | ⟨k, rfl⟩
    · exact iff_of_true (z.obj t).left (z'.obj t).left
    · exact iff_of_true (z.obj t).right (z'.obj t).right
    · have := congrArg (fun w ↦ (w.obj t).down k) h
      change (if _ ∈ (z.obj t).I then (1 : Fin 2) else 0) = if _ ∈ (z'.obj t).I then 1 else 0
        at this
      split_ifs at this with h₁ h₂ h₂ <;>
        first | exact iff_of_true h₁ h₂ | exact iff_of_false h₁ h₂ | exact absurd this (by decide)
  · change (if _ ∈ ((cubeInv n).obj (w.obj t)).I then (1 : Fin 2) else 0) = (w.obj t).down k
    rcases fin_two_cases ((w.obj t).down k) with h | h <;> simp [h, cubeInv]

variable (i) in
private noncomputable def box :
    ((⟨⟨0⟩⟩ : SimplicialThickening (ULift.{v} (Fin (n + 3)))) ⟶[SSet] ⟨⟨Fin.last _⟩⟩).Subcomplex :=
  (openBox (n + 1) i 0).preimage (nerveMap (cubeFun n))

variable {z : ((⟨⟨0⟩⟩ : SimplicialThickening (ULift.{v} (Fin (n + 3)))) ⟶[SSet]
  ⟨⟨Fin.last _⟩⟩).obj m}

open Classical in
private lemma mem_box_iff : z ∈ (box i).obj m ↔ ∃ k ε, (k, ε) ≠ (i, 0) ∧
    ∀ t, (if ⟨k.succ.castSucc⟩ ∈ (z.obj t).I then (1 : Fin 2) else 0) = ε := by
  simp only [box, openBox, Subcomplex.preimage_obj, Set.mem_preimage, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subtype.exists, Prod.exists, exists_prop]
  rfl

private lemma mem_box_of_fix {f : ⦋n + 2⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i.succ.castSucc f)
    (hfix : ∀ t, ∀ s ∈ (z.obj t).I, f.toOrderHom s.down = s.down) : z ∈ (box i).obj m := by
  obtain ⟨v, hv, hvr⟩ := hf
  rcases vertex_cases v with rfl | rfl | ⟨k, rfl⟩
  · exact absurd ⟨0, hfix 0 _ (z.obj 0).left⟩ hvr
  · exact absurd ⟨_, hfix 0 _ (z.obj 0).right⟩ hvr
  · exact mem_box_iff.2 ⟨k, 0, fun h ↦ hv (congrArg (·.succ.castSucc) (Prod.ext_iff.1 h).1),
      fun t ↦ if_neg fun hk ↦ hvr ⟨_, hfix t _ hk⟩⟩

private lemma box_cases (hz : z ∈ (box i).obj m) :
    (∃ f, InHorn i.succ.castSucc f ∧ ∀ t, ∀ s ∈ (z.obj t).I, f.toOrderHom s.down = s.down) ∨
      ∃ c, 0 < c ∧ c < Fin.last _ ∧ ∀ t, ⟨c⟩ ∈ (z.obj t).I := by
  obtain ⟨k, ε, hne, hz⟩ := mem_box_iff.1 hz
  rcases fin_two_cases ε with rfl | rfl
  · have hv (t) : ⟨k.succ.castSucc⟩ ∉ (z.obj t).I := fun h ↦
      absurd ((if_pos h).symm.trans (hz t)) (by decide)
    have h₀ : (0 : Fin (n + 3)) ≠ k.succ.castSucc := fun h ↦ by simpa using congrArg Fin.val h
    refine Or.inl ⟨retraction {s | s ≠ k.succ.castSucc} 0, ⟨k.succ.castSucc, fun h ↦ hne ?_,
      fun ⟨t, ht⟩ ↦ retraction_apply_mem (S := {s | s ≠ k.succ.castSucc}) h₀ t ht⟩,
      fun t s hs ↦ retraction_apply_of_mem (fun h ↦ hv t (h ▸ hs)) (Fin.zero_le _)⟩
    rw [Fin.succ_injective _ (Fin.castSucc_injective _ h)]
  · refine Or.inr ⟨k.succ.castSucc, Fin.castSucc_pos_iff.2 (Fin.succ_pos k),
      Fin.castSucc_lt_last _, fun t ↦ by_contra fun h ↦ ?_⟩
    exact absurd ((if_neg h).symm.trans (hz t)) (by decide)

open Classical in
private noncomputable def boxVal (z : ((⟨⟨0⟩⟩ : SimplicialThickening (ULift.{v} (Fin (n + 3))))
    ⟶[SSet] ⟨⟨Fin.last _⟩⟩).obj m) (hz : z ∈ (box i).obj m) :
    (vert σ₀ 0 ⟶[SSet] vert σ₀ (Fin.last _)).obj m :=
  if h : ∃ f, InHorn i.succ.castSucc f ∧ ∀ t, ∀ s ∈ (z.obj t).I, f.toOrderHom s.down = s.down then
    (hornMap σ₀ h.choose h.choose_spec.1 (h.choose_spec.2 0 _ (z.obj 0).left)
      (h.choose_spec.2 0 _ (z.obj 0).right)).app m z
  else
    have h' := (box_cases hz).resolve_left h
    (boxComp σ₀ h'.choose (Fin.zero_le _) (Fin.le_last _) h'.choose_spec.1
      h'.choose_spec.2.1).app m z

private lemma boxVal_of_fix (hz : z ∈ (box i).obj m) {f : ⦋n + 2⦌ ⟶ ⦋n + 2⦌}
    (hf : InHorn i.succ.castSucc f) (hfix : ∀ t, ∀ s ∈ (z.obj t).I, f.toOrderHom s.down = s.down)
    (ha : f.toOrderHom 0 = 0) (hb : f.toOrderHom (Fin.last _) = Fin.last _) :
    boxVal σ₀ z hz = (hornMap σ₀ f hf (a := ⟨⟨0⟩⟩) (b := ⟨⟨Fin.last _⟩⟩) ha hb).app m z := by
  have h : ∃ f, InHorn i.succ.castSucc f ∧ ∀ t, ∀ s ∈ (z.obj t).I, f.toOrderHom s.down = s.down :=
    ⟨f, hf, hfix⟩
  rw [boxVal, dif_pos h]
  exact hornMap_app_eq σ₀ _ _ _ _ _ _ z fun t s hs ↦
    (h.choose_spec.2 t s hs).trans (hfix t s hs).symm

private lemma boxVal_of_mem (hz : z ∈ (box i).obj m) {c : Fin (n + 3)} (h₀ : 0 < c)
    (hN : c < Fin.last _) (hc : ∀ t, ⟨c⟩ ∈ (z.obj t).I) :
    boxVal σ₀ z hz = (boxComp σ₀ c (Fin.zero_le _) (Fin.le_last _) h₀ hN).app m z := by
  rw [boxVal]
  split_ifs with hA
  · exact hornMap_app_eq_boxComp σ₀ _ _ _ z hA.choose_spec.2 _ _ _ _ hc
  · have hB := (box_cases hz).resolve_left hA
    rcases le_total hB.choose c with h | h
    · exact boxComp_app_eq σ₀ z h _ _ _ _ _ _ _ _ hB.choose_spec.2.2 hc
    · exact (boxComp_app_eq σ₀ z h _ _ _ _ _ _ _ _ hc hB.choose_spec.2.2).symm

private noncomputable def boxMap :
    (box i : SSet.{v}) ⟶ (vert σ₀ 0 ⟶[SSet] vert σ₀ (Fin.last _)) where
  app m := ↾fun z ↦ boxVal σ₀ z.1 z.2
  naturality m m' g := by
    ext z
    rcases box_cases z.2 with ⟨f, hf, hfix⟩ | ⟨c, h₀, hN, hc⟩
    · have ha := hfix 0 _ (z.1.obj 0).left
      have hb := hfix 0 _ (z.1.obj 0).right
      exact (boxVal_of_fix σ₀ ((box i : SSet).map g z).2 hf (fun t ↦ hfix _) ha hb).trans
        ((NatTrans.naturality_apply _ _ _).trans
          (congrArg _ (boxVal_of_fix σ₀ z.2 hf hfix ha hb).symm))
    · exact (boxVal_of_mem σ₀ ((box i : SSet).map g z).2 h₀ hN (fun t ↦ hc _)).trans
        ((NatTrans.naturality_apply _ _ _).trans (congrArg _ (boxVal_of_mem σ₀ z.2 h₀ hN hc).symm))

variable [KanComplex (vert σ₀ 0 ⟶[SSet] vert σ₀ (Fin.last _))]

private lemma hasLiftingProperty_box :
    HasLiftingProperty (box i).ι (terminal.from (vert σ₀ 0 ⟶[SSet] vert σ₀ (Fin.last _))) :=
  anodyneExtensions_preimage_ι _ (anodyneExtensions_openBox_ι (n + 1) i 0) _ (mem_fibrations _)

private noncomputable def filler :
    ((⟨⟨0⟩⟩ : SimplicialThickening (ULift.{v} (Fin (n + 3)))) ⟶[SSet] ⟨⟨Fin.last _⟩⟩) ⟶
      (vert σ₀ 0 ⟶[SSet] vert σ₀ (Fin.last _)) :=
  have := hasLiftingProperty_box σ₀
  (CommSq.mk (f := boxMap σ₀) (g := (box i).ι) (h := terminal.from _) (i := terminal.from _)
    (terminal.hom_ext _ _)).lift

private lemma filler_app (hz : z ∈ (box i).obj m) : (filler σ₀).app m z = boxVal σ₀ z hz :=
  have := hasLiftingProperty_box σ₀
  (NatTrans.comp_app_apply (box i).ι (filler σ₀) m ⟨z, hz⟩).symm.trans
    (congrArg (fun φ ↦ φ.app m ⟨z, hz⟩) (CommSq.fac_left (CommSq.mk (f := boxMap σ₀)
      (g := (box i).ι) (h := terminal.from _) (i := terminal.from _) (terminal.hom_ext _ _))))

private noncomputable def fillerAt {a b : Fin (n + 3)} (ha : a = 0) (hb : b = Fin.last _) :
    ((⟨⟨a⟩⟩ : SimplicialThickening (ULift.{v} (Fin (n + 3)))) ⟶[SSet] ⟨⟨b⟩⟩) ⟶
      (vert σ₀ a ⟶[SSet] vert σ₀ b) := by subst ha hb; exact filler σ₀

private noncomputable def fillMap (a b : SimplicialThickening (ULift.{v} (Fin (n + 3)))) :
    (a ⟶[SSet] b) ⟶ (vert σ₀ a.as.down ⟶[SSet] vert σ₀ b.as.down) :=
  if hab : a.as.down ≤ b.as.down then
    if h : a.as.down = 0 ∧ b.as.down = Fin.last _ then fillerAt σ₀ h.1 h.2
    else clampMap σ₀ hab ((not_and_or.1 h).imp Fin.pos_of_ne_zero Fin.lt_last_iff_ne_last.2)
  else (isInitialHom hab).to _

private lemma fillMap_of_ne (hab : a.as.down ≤ b.as.down)
    (h : ¬(a.as.down = 0 ∧ b.as.down = Fin.last _)) : fillMap σ₀ a b =
      clampMap σ₀ hab ((not_and_or.1 h).imp Fin.pos_of_ne_zero Fin.lt_last_iff_ne_last.2) := by
  rw [fillMap, dif_pos hab, dif_neg h]

private lemma fillMap_app_of_fix {f : ⦋n + 2⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i.succ.castSucc f)
    (ha : f.toOrderHom a.as.down = a.as.down) (hb : f.toOrderHom b.as.down = b.as.down)
    (z : (a ⟶[SSet] b).obj m) (hfix : ∀ t, ∀ s ∈ (z.obj t).I, f.toOrderHom s.down = s.down) :
    (fillMap σ₀ a b).app m z = (hornMap σ₀ f hf ha hb).app m z := by
  have hab : a.as ≤ b.as := Path.le (z.obj 0)
  rw [fillMap, dif_pos (ULift.down_le.2 hab)]
  split_ifs with h
  · obtain ⟨⟨a⟩⟩ := a
    obtain ⟨⟨b⟩⟩ := b
    dsimp only at h
    obtain ⟨rfl, rfl⟩ := h
    exact (filler_app σ₀ (mem_box_of_fix hf hfix)).trans (boxVal_of_fix σ₀ _ hf hfix ha hb)
  · exact (hornMap_app_eq_clampMap σ₀ hf ha hb _ _ z hfix).symm

private lemma fillMap_app_of_mem (z : (a ⟶[SSet] b).obj m) {c : Fin (n + 3)}
    (hac : a.as.down ≤ c) (hcb : c ≤ b.as.down) (h₀ : 0 < c) (hN : c < Fin.last _)
    (hc : ∀ t, ⟨c⟩ ∈ (z.obj t).I) :
    (fillMap σ₀ a b).app m z = (boxComp σ₀ c hac hcb h₀ hN).app m z := by
  rw [fillMap, dif_pos (hac.trans hcb)]
  split_ifs with h
  · obtain ⟨⟨a⟩⟩ := a
    obtain ⟨⟨b⟩⟩ := b
    dsimp only at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨k, rfl⟩ := ((vertex_cases c).resolve_left h₀.ne').resolve_left hN.ne
    exact (filler_app σ₀ (mem_box_iff.2 ⟨k, 1, by simp, fun t ↦ if_pos (hc t)⟩)).trans
      (boxVal_of_mem σ₀ _ h₀ hN hc)
  · exact hornMap_app_eq_boxComp σ₀ _ _ _ z (fix_clamp z le_rfl le_rfl) hac hcb h₀ hN hc

private lemma fillMap_comp_app {c : SimplicialThickening (ULift.{v} (Fin (n + 3)))}
    (p : (a ⟶[SSet] b).obj m) (q : (b ⟶[SSet] c).obj m) :
    (fillMap σ₀ a c).app m ((eComp SSet a b c).app m (p, q)) =
      (eComp SSet _ _ _).app m ((fillMap σ₀ a b).app m p, (fillMap σ₀ b c).app m q) := by
  have hab : a.as.down ≤ b.as.down := ULift.down_le.2 (Path.le (p.obj 0))
  have hbc : b.as.down ≤ c.as.down := ULift.down_le.2 (Path.le (q.obj 0))
  by_cases h : a.as.down = 0 ∧ c.as.down = Fin.last _
  · obtain ⟨⟨a⟩⟩ := a
    obtain ⟨⟨b⟩⟩ := b
    obtain ⟨⟨c⟩⟩ := c
    dsimp only at h hab hbc
    obtain ⟨rfl, rfl⟩ := h
    rcases vertex_cases b with rfl | rfl | ⟨k, rfl⟩
    · obtain rfl : p = (eId SSet _).app m PUnit.unit :=
        nerve.ext_of_isThin (funext fun _ ↦ Subsingleton.elim _ _)
      rw [eComp_eId_app, fillMap_of_ne σ₀ (a := ⟨⟨0⟩⟩) (b := ⟨⟨0⟩⟩) le_rfl
        fun h ↦ Fin.last_pos'.ne h.2, clampMap_eId_app, eComp_eId_app]
    · obtain rfl : q = (eId SSet _).app m PUnit.unit :=
        nerve.ext_of_isThin (funext fun _ ↦ Subsingleton.elim _ _)
      rw [eComp_eId_app', fillMap_of_ne σ₀ (a := ⟨⟨Fin.last _⟩⟩) (b := ⟨⟨Fin.last _⟩⟩) le_rfl
        fun h ↦ Fin.last_pos'.ne h.1.symm, clampMap_eId_app, eComp_eId_app']
    · have h₀ : 0 < k.succ.castSucc := Fin.castSucc_pos_iff.2 (Fin.succ_pos k)
      have e := restrict_eComp (J := ULift.{v} (Fin (n + 3))) hab hbc p q
      rw [fillMap_app_of_mem σ₀ ((eComp SSet _ _ _).app m (p, q)) hab hbc h₀
        (Fin.castSucc_lt_last _) (fun t ↦ Or.inl (p.obj t).right), boxComp_app, e.1, e.2,
        fillMap_of_ne σ₀ hab fun h ↦ (Fin.castSucc_lt_last _).ne h.2,
        fillMap_of_ne σ₀ hbc fun h ↦ h₀.ne' h.1]
  · have hf := inHorn_clamp (i := i) (hab.trans hbc)
      ((not_and_or.1 h).imp Fin.pos_of_ne_zero Fin.lt_last_iff_ne_last.2)
    have hac := hab.trans hbc
    rw [fillMap_app_of_fix σ₀ hf (clamp_apply le_rfl hac) (clamp_apply hac le_rfl) _
        (fix_clamp _ le_rfl le_rfl), hornMap_comp_app σ₀ hf _ _ (clamp_apply hab hbc),
      fillMap_app_of_fix σ₀ hf (clamp_apply le_rfl hac) _ p (fix_clamp p le_rfl hbc),
      fillMap_app_of_fix σ₀ hf _ (clamp_apply hac le_rfl) q (fix_clamp q hab le_rfl)]

private noncomputable def fill :
    EnrichedFunctor SSet (SimplicialThickening (ULift.{v} (Fin (n + 3)))) C where
  obj a := vert σ₀ a.as.down
  map := fillMap σ₀
  map_id a := by
    have h : ¬(a.as.down = 0 ∧ a.as.down = Fin.last _) := fun h ↦
      Fin.last_pos'.ne (h.1.symm.trans h.2)
    rw [fillMap_of_ne σ₀ le_rfl h]
    ext m u
    exact clampMap_eId_app σ₀ ((not_and_or.1 h).imp Fin.pos_of_ne_zero Fin.lt_last_iff_ne_last.2)
  map_comp a b c := by
    ext m ⟨p, q⟩
    exact fillMap_comp_app σ₀ p q

private lemma δ_fill (j : Fin (n + 3)) (hj : j ≠ i.succ.castSucc) :
    (SimplicialNerve C).δ j (fill σ₀) = σ₀.app _ (horn.face _ j hj) := by
  let g := SimplexCategory.δ j
  have hg : InHorn i.succ.castSucc g := ⟨j, hj, fun ⟨s, hs⟩ ↦ Fin.succAbove_ne j s hs⟩
  let r := retraction (Set.range g.toOrderHom) (g.toOrderHom 0)
  have hr : InHorn i.succ.castSucc r := by
    obtain ⟨t, ht, ht'⟩ := hg
    exact ⟨t, ht, fun ⟨s, hs⟩ ↦
      ht' (hs ▸ retraction_apply_mem (S := Set.range g.toOrderHom) ⟨0, rfl⟩ s)⟩
  have hfix (s) : r.toOrderHom (g.toOrderHom s) = g.toOrderHom s :=
    retraction_apply_of_mem ⟨s, rfl⟩ (g.toOrderHom.monotone (Fin.zero_le s))
  have e : (functor g.toOrderHom.uliftMap).comp SSet (fill σ₀) = hornVal σ₀ g hg := by
    refine EnrichedFunctor.ext _ (fun a ↦ (hornVal_obj σ₀ _ hg a).symm) fun a b ↦ ?_
    have : (functor g.toOrderHom.uliftMap).map a b ≫ fillMap σ₀ _ _ =
        hornMap σ₀ g hg rfl rfl := by
      ext m z
      refine (fillMap_app_of_fix σ₀ (a := (functor g.toOrderHom.uliftMap).obj a)
        (b := (functor g.toOrderHom.uliftMap).obj b) hr (hfix _) (hfix _) _ ?_).trans ?_
      · rintro t _ ⟨s, -, rfl⟩
        exact hfix s.down
      · exact (congrArg (fun φ ↦ φ.app m z) (hornMap_comp σ₀ g _ hr (a := a) (b := b) (hfix _)
          (hfix _))).symm.trans (hornMap_app_eq σ₀ _ _ _ _ _ _ z fun t s _ ↦ hfix s.down)
    exact (congrArg (· ≫ eqToHom _) this).trans ((Category.assoc _ _ _).trans
      ((congrArg _ (eqToHom_trans _ _)).trans ((congrArg _ (eqToHom_refl _ _)).trans
        (Category.comp_id _))))
  exact e

end Filler

theorem quasicategory_simplicialNerve (C : Type u) [Category.{v} C] [SimplicialCategory C]
    (hC : ∀ x y : C, (sHom x y).KanComplex) : (SimplicialNerve C).Quasicategory := by
  refine quasicategory_of_filler _ fun n i σ₀ h₀ hN ↦ ?_
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hN.ne
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (Fin.castSucc_ne_zero_iff.1 h₀.ne')
  have := hC (vert σ₀ 0) (vert σ₀ (Fin.last _))
  exact ⟨fill σ₀, fun j hj ↦ δ_fill σ₀ j hj⟩

instance quasicategory [hC : ∀ x y : C, (sHom x y).KanComplex] :
    (SimplicialNerve C).Quasicategory :=
  quasicategory_simplicialNerve C hC

end SimplicialNerve

end CategoryTheory
