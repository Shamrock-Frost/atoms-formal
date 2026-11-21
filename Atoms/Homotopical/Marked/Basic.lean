import Atoms.ForMathlib.CategoryTheory.Topos.Separated
import Atoms.Homotopical.Cellular.Model
import Atoms.Homotopical.Marked.Site

open CategoryTheory Limits Opposite MorphismProperty

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A] (D : MarkingData A)

abbrev MarkedPresheaf : Type (max w v + 1) :=
  SeparatedPresheaf.{max w v} (MarkedSite.topology D)

namespace MarkedPresheaf

open MarkedSite

variable {D}

theorem injective_map_toSelf (X : MarkedPresheaf.{w} D) (x : MarkedSite D) :
    Function.Injective (X.obj.map (toSelf x).op) :=
  isSeparated_iff.1 X.2 x

abbrev underlying (X : MarkedPresheaf.{w} D) : Aᵒᵖ ⥤ Type (max w v) :=
  (unmarked D).op ⋙ X.obj

def marked (X : MarkedPresheaf.{w} D) (a : A) : Set (X.underlying.obj (op a)) :=
  {x | ∃ (h : D.markable a) (y : X.obj.obj (op (MarkedSite.marked a h))),
    X.obj.map (toSelf (MarkedSite.marked a h)).op y = x}

theorem map_toSelf_map (X : MarkedPresheaf.{w} D) {x y : MarkedSite D} (g : x ⟶ y)
    (s : X.obj.obj (op y)) :
    X.obj.map (toSelf x).op (X.obj.map g.op s) =
      X.underlying.map g.1.op (X.obj.map (toSelf y).op s) := by
  rw [← Functor.map_comp_apply, ← op_comp, toSelf_comp, op_comp, Functor.map_comp_apply]
  rfl

theorem map_toSelf_unmarked (X : MarkedPresheaf.{w} D) (a : A) (s : X.underlying.obj (op a)) :
    X.obj.map (toSelf ((unmarked D).obj a)).op s = s :=
  Functor.map_id_apply X.obj _ s

theorem markable (X : MarkedPresheaf.{w} D) (a : A) (x : X.underlying.obj (op a))
    (hx : x ∈ X.marked a) : D.markable a :=
  hx.1

theorem degenerate (X : MarkedPresheaf.{w} D) ⦃a b : A⦄ (p : a ⟶ b) (hp : D.degeneracy p)
    (y : X.underlying.obj (op b)) : X.underlying.map p.op y ∈ X.marked a := by
  let g : MarkedSite.marked a (D.markable_of_degeneracy p hp) ⟶ (unmarked D).obj b :=
    ⟨p, fun _ => Or.inr (.of_degeneracy hp)⟩
  refine ⟨D.markable_of_degeneracy p hp, X.obj.map g.op y, ?_⟩
  rw [map_toSelf_map, map_toSelf_unmarked]
  rfl

private theorem map_mem_marked_of_iso (X : MarkedPresheaf.{w} D) {a b : A} (e : a ≅ b)
    {x : X.underlying.obj (op b)} (hx : x ∈ X.marked b) :
    X.underlying.map e.hom.op x ∈ X.marked a := by
  obtain ⟨h, y, rfl⟩ := hx
  let g : MarkedSite.marked a (D.markable_of_iso e h) ⟶ MarkedSite.marked b h :=
    ⟨e.hom, fun _ => Or.inl ⟨rfl, Iso.isIso_hom e⟩⟩
  exact ⟨D.markable_of_iso e h, X.obj.map g.op y, map_toSelf_map X g y⟩

theorem transport (X : MarkedPresheaf.{w} D) ⦃a b : A⦄ (e : a ≅ b) (x : X.underlying.obj (op b)) :
    x ∈ X.marked b ↔ X.underlying.map e.hom.op x ∈ X.marked a := by
  refine ⟨map_mem_marked_of_iso X e, fun h => ?_⟩
  have := map_mem_marked_of_iso X e.symm h
  rwa [Iso.symm_hom, ← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, op_id,
    Functor.map_id_apply] at this

def forget : MarkedPresheaf.{w} D ⥤ Aᵒᵖ ⥤ Type (max w v) :=
  ObjectProperty.ι _ ⋙ (Functor.whiskeringLeft _ _ _).obj (unmarked D).op

@[simp]
theorem forget_obj (X : MarkedPresheaf.{w} D) : forget.obj X = X.underlying := rfl

theorem forget_map_app_map_toSelf {X Y : MarkedPresheaf.{w} D} (f : X ⟶ Y) (x : MarkedSite D)
    (s : X.obj.obj (op x)) :
    (forget.map f).app (op x.obj) (X.obj.map (toSelf x).op s) =
      Y.obj.map (toSelf x).op (f.hom.app (op x) s) := by
  change f.hom.app _ (X.obj.map (toSelf x).op s) = _
  exact NatTrans.naturality_apply f.hom (toSelf x).op s

theorem map_mem_marked {X Y : MarkedPresheaf.{w} D} (f : X ⟶ Y) {a : A}
    {x : X.underlying.obj (op a)} (hx : x ∈ X.marked a) :
    (forget.map f).app (op a) x ∈ Y.marked a := by
  obtain ⟨h, y, rfl⟩ := hx
  exact ⟨h, f.hom.app _ y, (forget_map_app_map_toSelf f _ y).symm⟩

theorem hom_ext {X Y : MarkedPresheaf.{w} D} {f g : X ⟶ Y} (h : forget.map f = forget.map g) :
    f = g := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun x => ?_))
  ext s
  apply Y.injective_map_toSelf x.unop
  change Y.obj.map (toSelf x.unop).op (f.hom.app (op x.unop) s) =
    Y.obj.map (toSelf x.unop).op (g.hom.app (op x.unop) s)
  rw [← forget_map_app_map_toSelf, ← forget_map_app_map_toSelf, h]

instance faithful_forget : (forget (D := D)).Faithful where
  map_injective h := hom_ext h

section HomMk

variable {X Y : MarkedPresheaf.{w} D} (f : X.underlying ⟶ Y.underlying)
  (hf : ∀ (a : A) (x : X.underlying.obj (op a)), x ∈ X.marked a → f.app (op a) x ∈ Y.marked a)

private noncomputable def homMkApp : ∀ x : MarkedSite D, X.obj.obj (op x) → Y.obj.obj (op x)
  | ⟨a, false, _⟩, s => f.app (op a) s
  | ⟨a, true, h⟩, s => (hf a _ ⟨h rfl, s, rfl⟩).choose_spec.choose

private theorem map_toSelf_homMkApp (x : MarkedSite D) (s : X.obj.obj (op x)) :
    Y.obj.map (toSelf x).op (homMkApp f hf x s) = f.app (op x.obj) (X.obj.map (toSelf x).op s) := by
  obtain ⟨a, _ | _, h⟩ := x
  · exact (Y.map_toSelf_unmarked a _).trans (congrArg (f.app (op a))
      (X.map_toSelf_unmarked a s).symm)
  · exact (hf a _ ⟨h rfl, s, rfl⟩).choose_spec.choose_spec

noncomputable def homMk : X ⟶ Y :=
  ObjectProperty.homMk
    { app x := ↾homMkApp f hf x.unop
      naturality x y g := by
        ext s
        apply Y.injective_map_toSelf y.unop
        change Y.obj.map (toSelf y.unop).op (homMkApp f hf y.unop (X.obj.map g.unop.op s)) =
          Y.obj.map (toSelf y.unop).op (Y.obj.map g.unop.op (homMkApp f hf x.unop s))
        rw [map_toSelf_homMkApp, map_toSelf_map, Y.map_toSelf_map, map_toSelf_homMkApp]
        exact NatTrans.naturality_apply f g.unop.1.op _ }

@[simp]
theorem forget_map_homMk : forget.map (homMk f hf) = f := rfl

end HomMk

section OfMarking

variable (D) in
@[ext]
structure Marking (P : Aᵒᵖ ⥤ Type (max w v)) where
  marked : ∀ a : A, Set (P.obj (op a))
  markable : ∀ (a : A) (x : P.obj (op a)), x ∈ marked a → D.markable a
  degenerate : ∀ ⦃a b : A⦄ (p : a ⟶ b), D.degeneracy p → ∀ y, P.map p.op y ∈ marked a
  transport : ∀ ⦃a b : A⦄ (e : a ≅ b) (x : P.obj (op b)),
    x ∈ marked b ↔ P.map e.hom.op x ∈ marked a

namespace Marking

variable {P : Aᵒᵖ ⥤ Type (max w v)} (M : Marking D P)

private def obj : MarkedSite D → Type (max w v)
  | ⟨a, false, _⟩ => P.obj (op a)
  | ⟨a, true, _⟩ => M.marked a

private def val : ∀ x : MarkedSite D, M.obj x → P.obj (op x.obj)
  | ⟨_, false, _⟩, c => c
  | ⟨_, true, _⟩, c => c.1

private def cell :
    ∀ (x : MarkedSite D) (c : P.obj (op x.obj)), (x.isMarked = true → c ∈ M.marked x.obj) →
      M.obj x
  | ⟨_, false, _⟩, c, _ => c
  | ⟨_, true, _⟩, c, h => ⟨c, h rfl⟩

@[simp]
private theorem val_cell (x : MarkedSite D) (c : P.obj (op x.obj))
    (h : x.isMarked = true → c ∈ M.marked x.obj) : M.val x (M.cell x c h) = c := by
  obtain ⟨a, _ | _, _⟩ := x <;> rfl

private theorem val_mem (x : MarkedSite D) (s : M.obj x) (hx : x.isMarked = true) :
    M.val x s ∈ M.marked x.obj := by
  obtain ⟨a, _ | _, _⟩ := x
  · exact absurd hx Bool.false_ne_true
  · exact s.2

private theorem val_injective (x : MarkedSite D) : Function.Injective (M.val x) := by
  obtain ⟨a, _ | _, _⟩ := x
  · exact fun _ _ h => h
  · exact Subtype.val_injective

private theorem map_mem {x y : MarkedSite D} (g : x ⟶ y) (s : M.obj y) (hx : x.isMarked = true) :
    P.map g.1.op (M.val y s) ∈ M.marked x.obj := by
  rcases g.2 hx with ⟨hy, hg⟩ | ⟨d, p, q, hp, hpq⟩
  · exact (M.transport (asIso g.1) _).1 (M.val_mem y s hy)
  · rw [← hpq, op_comp, Functor.map_comp, types_comp_apply]
    exact M.degenerate p hp _

private def toPresheaf : (MarkedSite D)ᵒᵖ ⥤ Type (max w v) where
  obj x := M.obj x.unop
  map g := ↾fun s => M.cell _ (P.map g.unop.1.op (M.val _ s)) fun hx => M.map_mem g.unop s hx
  map_id x := by
    ext s
    exact M.val_injective _ ((M.val_cell _ _ _).trans (Functor.map_id_apply P _ _))
  map_comp f g := by
    ext s
    refine M.val_injective _ ((M.val_cell _ _ _).trans ?_)
    change P.map (g.unop.1 ≫ f.unop.1).op (M.val _ s) =
      M.val _ (M.cell _ (P.map g.unop.1.op
        (M.val _ (M.cell _ (P.map f.unop.1.op (M.val _ s)) _))) _)
    rw [M.val_cell, M.val_cell, op_comp, Functor.map_comp_apply]

private theorem isSeparated_toPresheaf : Presieve.IsSeparated (topology D) M.toPresheaf :=
  isSeparated_iff.2 fun x s t h => M.val_injective x (by
    have := congrArg (M.val ((unmarked D).obj x.obj)) h
    change P.map (𝟙 (op x.obj)) (M.val x s) = P.map (𝟙 (op x.obj)) (M.val x t) at this
    rwa [Functor.map_id_apply, Functor.map_id_apply] at this)

end Marking

def ofMarking (P : Aᵒᵖ ⥤ Type (max w v)) (M : Marking D P) : MarkedPresheaf.{w} D :=
  ⟨M.toPresheaf, M.isSeparated_toPresheaf⟩

theorem ofMarking_congr (P : Aᵒᵖ ⥤ Type (max w v)) {M M' : Marking D P}
    (h : ∀ a, M.marked a = M'.marked a) : ofMarking P M = ofMarking P M' :=
  congrArg (ofMarking P) (Marking.ext (funext h))

@[simp]
theorem underlying_ofMarking (P : Aᵒᵖ ⥤ Type (max w v)) (M : Marking D P) :
    (ofMarking P M).underlying = P := rfl

@[simp]
theorem mem_marked_ofMarking (P : Aᵒᵖ ⥤ Type (max w v)) (M : Marking D P) (a : A)
    (x : P.obj (op a)) :
    x ∈ (ofMarking P M).marked a ↔ x ∈ M.marked a := by
  constructor
  · rintro ⟨h, y, rfl⟩
    exact (congrArg (· ∈ M.marked a) (Functor.map_id_apply P _ y.1)).mpr y.2
  · intro hx
    exact ⟨M.markable a x hx, ⟨x, hx⟩, Functor.map_id_apply P _ x⟩

end OfMarking

variable (D)

def flatMarking (P : Aᵒᵖ ⥤ Type (max w v)) : Marking D P where
  marked a := {x | ∃ (b : A) (p : a ⟶ b), D.degeneracy p ∧ ∃ y, P.map p.op y = x}
  markable a _ := fun ⟨_, p, hp, _⟩ => D.markable_of_degeneracy p hp
  degenerate _ _ p hp y := ⟨_, p, hp, y, rfl⟩
  transport a b e x := by
    have := D.respectsIso
    constructor
    · rintro ⟨c, p, hp, y, rfl⟩
      refine ⟨c, e.hom ≫ p, (D.degeneracy.cancel_left_of_respectsIso e.hom p).2 hp, y, ?_⟩
      simp
    · rintro ⟨c, p, hp, y, hy⟩
      refine ⟨c, e.inv ≫ p, (D.degeneracy.cancel_left_of_respectsIso e.inv p).2 hp, y, ?_⟩
      rw [op_comp, Functor.map_comp, types_comp_apply, hy, ← types_comp_apply (P.map _),
        ← Functor.map_comp, ← op_comp, e.inv_hom_id, op_id, Functor.map_id_apply]

def sharpMarking (P : Aᵒᵖ ⥤ Type (max w v)) : Marking D P where
  marked a := {_x | D.markable a}
  markable _ _ h := h
  degenerate _ _ p hp _ := D.markable_of_degeneracy p hp
  transport _ _ e _ := ⟨fun h => D.markable_of_iso e h, fun h => D.markable_of_iso e.symm h⟩

noncomputable def flat : (Aᵒᵖ ⥤ Type (max w v)) ⥤ MarkedPresheaf.{w} D where
  obj P := ofMarking P (flatMarking D P)
  map {P Q} f := homMk (X := ofMarking P (flatMarking D P)) f fun a _ hx => by
    obtain ⟨b, p, hp, y, rfl⟩ := (mem_marked_ofMarking _ _ a _).1 hx
    exact (mem_marked_ofMarking _ _ a _).2
      ⟨b, p, hp, f.app _ y, (NatTrans.naturality_apply f p.op y).symm⟩
  map_id _ := hom_ext rfl
  map_comp _ _ := hom_ext rfl

noncomputable def sharp : (Aᵒᵖ ⥤ Type (max w v)) ⥤ MarkedPresheaf.{w} D where
  obj P := ofMarking P (sharpMarking D P)
  map {P _} f := homMk (X := ofMarking P (sharpMarking D P)) f fun a _ hx =>
    (mem_marked_ofMarking _ _ a _).2 ((ofMarking P (sharpMarking D P)).markable a _ hx)
  map_id _ := hom_ext rfl
  map_comp _ _ := hom_ext rfl

@[simp]
theorem mem_marked_flat (P : Aᵒᵖ ⥤ Type (max w v)) (a : A) (x : P.obj (op a)) :
    x ∈ ((flat D).obj P).marked a ↔ ∃ (b : A) (p : a ⟶ b), D.degeneracy p ∧ ∃ y, P.map p.op y = x :=
  mem_marked_ofMarking _ _ _ _

noncomputable def flatForgetAdjunction : flat D ⊣ forget (D := D) :=
  Adjunction.mkOfHomEquiv
    { homEquiv P X :=
        { toFun g := forget.map g
          invFun φ := homMk (X := (flat D).obj P) φ (by
            rintro a _ hx
            obtain ⟨b, p, hp, y, rfl⟩ := (mem_marked_flat D P a _).1 hx
            exact (NatTrans.naturality_apply φ p.op y) ▸ X.degenerate p hp (φ.app _ y))
          left_inv _ := hom_ext rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := hom_ext rfl
      homEquiv_naturality_right _ _ := rfl }

@[simp]
theorem mem_marked_sharp (P : Aᵒᵖ ⥤ Type (max w v)) (a : A) (x : P.obj (op a)) :
    x ∈ ((sharp D).obj P).marked a ↔ D.markable a :=
  mem_marked_ofMarking _ _ _ _

noncomputable def forgetSharpAdjunction : forget (D := D) ⊣ sharp D :=
  Adjunction.mkOfHomEquiv
    { homEquiv X P :=
        { toFun φ := homMk (Y := (sharp D).obj P) φ fun a x hx =>
            (mem_marked_sharp D P a _).2 (X.markable a x hx)
          invFun ψ := forget.map ψ
          left_inv _ := rfl
          right_inv _ := hom_ext rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := hom_ext rfl }

theorem flat_comp_forget : flat D ⋙ forget = 𝟭 _ := rfl

theorem sharp_comp_forget : sharp D ⋙ forget = 𝟭 _ := rfl

instance full_flat : (flat D).Full where
  map_surjective f := ⟨forget.map f, hom_ext rfl⟩

instance faithful_flat : (flat D).Faithful where
  map_injective h := congrArg forget.map h

noncomputable def isTerminalSharpTerminal :
    IsTerminal ((sharp D).obj (⊤_ (Aᵒᵖ ⥤ Type (max w v)))) :=
  IsTerminal.ofUniqueHom (fun _ => (forgetSharpAdjunction D).homEquiv _ _ (terminal.from _))
    fun _ _ => hom_ext (terminal.hom_ext _ _)

theorem hasLiftingProperty_terminal_from_sharp_iff {X Y : MarkedPresheaf.{w} D} (i : X ⟶ Y)
    (P : Aᵒᵖ ⥤ Type (max w v)) : HasLiftingProperty i (terminal.from ((sharp D).obj P)) ↔
      HasLiftingProperty (forget.map i) (terminal.from P) := by
  let e : Arrow.mk (terminal.from ((sharp D).obj P)) ≅ Arrow.mk ((sharp D).map (terminal.from P)) :=
    Arrow.isoMk (Iso.refl _) (terminalIsoIsTerminal (isTerminalSharpTerminal D))
      ((isTerminalSharpTerminal D).hom_ext _ _)
  rw [(forgetSharpAdjunction D).hasLiftingProperty_iff]
  exact ⟨fun _ => HasLiftingProperty.of_arrow_iso_right i e,
    fun _ => HasLiftingProperty.of_arrow_iso_right i e.symm⟩

instance isLeftAdjoint_forget : (forget (D := D)).IsLeftAdjoint :=
  (forgetSharpAdjunction D).isLeftAdjoint

instance isRightAdjoint_forget : (forget (D := D)).IsRightAdjoint :=
  (flatForgetAdjunction D).isRightAdjoint

variable {D}

theorem mono_iff {X Y : MarkedPresheaf.{w} D} (f : X ⟶ Y) : Mono f ↔ Mono (forget.map f) :=
  ⟨fun _ => forget.map_mono f, fun _ => forget.mono_of_mono_map ‹_›⟩

variable (D)

theorem monomorphisms_eq :
    monomorphisms (MarkedPresheaf.{w} D) =
      (monomorphisms (Aᵒᵖ ⥤ Type (max w v))).inverseImage forget := by
  ext X Y f
  exact mono_iff f

instance isSaturated_monomorphisms :
    IsSaturated.{max w v} (monomorphisms (MarkedPresheaf.{w} D)) := by
  rw [monomorphisms_eq]
  infer_instance

instance isStableUnderFilteredColimits_monomorphisms :
    (monomorphisms (MarkedPresheaf.{w} D)).IsStableUnderFilteredColimits.{max w v, max w v} where
  isStableUnderColimitsOfShape J _ _ := ⟨fun X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ => by
    rw [monomorphisms.iff, mono_iff]
    exact colimitsOfShape_le (W := monomorphisms (Aᵒᵖ ⥤ Type (max w v))) (J := J) _
      (colimitsOfShape.mk' (X₁ ⋙ forget) (X₂ ⋙ forget) _ _ (isColimitOfPreserves forget h₁)
        (isColimitOfPreserves forget h₂) (Functor.whiskerRight f forget)
        (fun j => (mono_iff _).1 (hf j)) (forget.map φ)
        fun j => (forget.map_comp _ _).symm.trans ((congrArg forget.map (hφ j)).trans
          (forget.map_comp _ _)))⟩

instance hasCellularModel : HasCellularModel (MarkedPresheaf.{w} D) :=
  HasCellularModel.ofAdjunction (SeparatedPresheaf.adjunction _)

noncomputable instance monoidalClosed : MonoidalClosed (MarkedPresheaf.{w} D) :=
  Quasitopos.monoidalClosed

noncomputable instance braidedCategory : BraidedCategory (MarkedPresheaf.{w} D) :=
  .ofCartesianMonoidalCategory

variable {D}

theorem exists_forget_map_eq_of_isColimit {J : Type*} [Category J]
    {F : J ⥤ MarkedPresheaf.{w} D} {c : Cocone F} (hc : IsColimit c) {b : A}
    (z : c.pt.underlying.obj (op b)) :
    ∃ (j : J) (x : (F.obj j).underlying.obj (op b)), (forget.map (c.ι.app j)).app (op b) x = z := by
  let hc' := isColimitOfPreserves forget hc
  let S : Subfunctor c.pt.underlying := ⨆ j, Subfunctor.range (forget.map (c.ι.app j))
  let s : Cocone (F ⋙ forget) :=
    { pt := S.toFunctor
      ι := { app j := Subfunctor.lift (forget.map (c.ι.app j))
               (le_iSup (fun j => Subfunctor.range (forget.map (c.ι.app j))) j)
             naturality _ _ g := by
               ext b x
               have := ConcreteCategory.congr_hom (NatTrans.congr_app
                 ((Functor.map_comp _ _ _).symm.trans
                   (congrArg forget.map ((c.ι.naturality g).trans (Category.comp_id _)))) b) x
               exact Subtype.ext this } }
  have h : hc'.desc s ≫ S.ι = 𝟙 _ := hc'.hom_ext fun j =>
    (hc'.fac_assoc s j S.ι).trans (Category.comp_id _).symm
  have hz := ((hc'.desc s).app (op b) z).2
  have hd : ((hc'.desc s).app (op b) z).1 = z := congrArg (fun φ => φ.app (op b) z) h
  rw [hd, Subfunctor.iSup_obj, Set.mem_iUnion] at hz
  obtain ⟨j, x, hx⟩ := hz
  exact ⟨j, x, hx⟩

theorem exists_mem_marked_of_isColimit {J : Type*} [Category J] {F : J ⥤ MarkedPresheaf.{w} D}
    {c : Cocone F} (hc : IsColimit c) {a : A} {y : c.pt.underlying.obj (op a)}
    (hy : y ∈ c.pt.marked a) :
    ∃ (j : J) (x : (F.obj j).underlying.obj (op a)), x ∈ (F.obj j).marked a ∧
      (forget.map (c.ι.app j)).app (op a) x = y := by
  have hs (b : A) (z : c.pt.underlying.obj (op b)) := exists_forget_map_eq_of_isColimit hc z
  let M : Marking D c.pt.underlying :=
    { marked b := {z | ∃ (j : J) (x : (F.obj j).underlying.obj (op b)), x ∈ (F.obj j).marked b ∧
        (forget.map (c.ι.app j)).app (op b) x = z}
      markable b _ := fun ⟨j, x, hx, _⟩ => (F.obj j).markable b x hx
      degenerate b _ p hp z := by
        obtain ⟨j, x, rfl⟩ := hs _ z
        exact ⟨j, _, (F.obj j).degenerate p hp x,
          NatTrans.naturality_apply (forget.map (c.ι.app j)) p.op x⟩
      transport b b' e z := by
        constructor
        · rintro ⟨j, x, hx, rfl⟩
          exact ⟨j, _, ((F.obj j).transport e x).1 hx,
            NatTrans.naturality_apply (forget.map (c.ι.app j)) e.hom.op x⟩
        · rintro ⟨j, x, hx, hxz⟩
          refine ⟨j, (F.obj j).underlying.map e.inv.op x, ((F.obj j).transport e.symm x).1 hx, ?_⟩
          refine (NatTrans.naturality_apply (forget.map (c.ι.app j)) e.inv.op x).trans
            ((congrArg (c.pt.underlying.map e.inv.op) hxz).trans ?_)
          rw [← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, op_id, Functor.map_id_apply] }
  let c' : Cocone F :=
    { pt := ofMarking _ M
      ι := { app j := homMk (Y := ofMarking _ M) (forget.map (c.ι.app j)) fun b x hx =>
               (mem_marked_ofMarking _ _ _ _).2 ⟨j, x, hx, rfl⟩
             naturality _ _ g := hom_ext ((Functor.map_comp _ _ _).symm.trans
               ((congrArg forget.map ((c.ι.naturality g).trans
                 (Category.comp_id _))).trans (Category.comp_id _).symm)) } }
  let incl : c'.pt ⟶ c.pt := homMk (𝟙 _) fun b z hz => by
    obtain ⟨j, x, hx, rfl⟩ := (mem_marked_ofMarking _ _ _ _).1 hz
    exact map_mem_marked (c.ι.app j) hx
  have h : hc.desc c' ≫ incl = 𝟙 _ := hc.hom_ext fun j => by
    rw [hc.fac_assoc, Category.comp_id]
    exact hom_ext rfl
  have hd : (forget.map (hc.desc c')).app _ y = y :=
    congrArg (fun φ => (forget.map φ).app _ y) h
  have := map_mem_marked (hc.desc c') hy
  rw [hd] at this
  exact (mem_marked_ofMarking _ _ _ _).1 this

end MarkedPresheaf

end Atoms.Homotopical
