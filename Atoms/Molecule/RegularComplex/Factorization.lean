import Atoms.Molecule.Pushforward
import Atoms.Molecule.RegularComplex.CartesianAtom
import Atoms.Molecule.RegularComplex.ComapPullback

universe u v w

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

def IsMap.range {P : OGP.{u}} {Q : OGP.{v}} {f : P → Q} (hf : IsMap f) : LowerSet Q :=
  ⟨Set.range f, by simpa only [image_univ] using hf.fibration.isLowerSet_image isLowerSet_univ⟩

@[simp] theorem IsMap.coe_range {P : OGP.{u}} {Q : OGP.{v}} {f : P → Q} (hf : IsMap f) :
    (hf.range : Set Q) = Set.range f :=
  rfl

theorem IsMap.of_comp_of_injective {P : OGP.{u}} {R S : OGP.{v}} {f : P → R} {g : R → S}
    (hg : IsMap g) (hi : Function.Injective g) (h : IsMap (g ∘ f)) : IsMap f :=
  letI : IsInclusion (ConcreteCategory.ofHom (C := OGP.{v}) ⟨g, hg.isMorphism_of_injective hi⟩) :=
    ⟨hi⟩
  IsMap.of_comp (ConcreteCategory.ofHom (C := OGP.{v}) ⟨g, hg.isMorphism_of_injective hi⟩) h

namespace RDCpxDown

def surjective : MorphismProperty RDCpxDown.{u} := fun _ _ f =>
  Function.Surjective (ConcreteCategory.hom f)

def inclusions : MorphismProperty RDCpxDown.{u} := fun _ _ f =>
  Function.Injective (ConcreteCategory.hom f)

instance : surjective.{u}.IsMultiplicative where
  id_mem _ := Function.surjective_id
  comp_mem _ _ hf hg := hg.comp hf

instance : inclusions.{u}.IsMultiplicative where
  id_mem _ := Function.injective_id
  comp_mem _ _ hf hg := hg.comp hf

variable {P Q : RDCpxDown.{u}}

def image (p : P ⟶ Q) : RDCpxDown.{u} :=
  ⟨Q.toOGP.restrict (ConcreteCategory.hom p).isMap.range, Q.isRDC.restrict _⟩

def toImage (p : P ⟶ Q) : P ⟶ image p :=
  ConcreteCategory.ofHom (X := P) (Y := image p)
    ⟨_, (ConcreteCategory.hom p).isMap.codRestrict fun x => Set.mem_range_self x⟩

def imageι (p : P ⟶ Q) : image p ⟶ Q :=
  ConcreteCategory.ofHom (X := image p) (Y := Q) ⟨_, isMap_of_isInclusion (incl _)⟩

@[reassoc (attr := simp)]
theorem toImage_imageι (p : P ⟶ Q) : toImage p ≫ imageι p = p := by
  ext x
  rfl

theorem surjective_toImage (p : P ⟶ Q) : surjective (toImage p) := by
  rintro ⟨_, x, rfl⟩
  exact ⟨x, rfl⟩

theorem inclusions_imageι (p : P ⟶ Q) : inclusions (imageι p) :=
  Subtype.val_injective

theorem hom_ext_of_inclusions {A X Y : RDCpxDown.{u}} {i : X ⟶ Y} (hi : inclusions i)
    {f g : A ⟶ X} (h : f ≫ i = g ≫ i) : f = g := by
  ext x
  exact hi (ConcreteCategory.congr_hom h x)

theorem hasLiftingProperty_of_surjective_of_inclusions {A B X Y : RDCpxDown.{u}}
    (s : A ⟶ B) (i : X ⟶ Y) (hs : surjective s) (hi : inclusions i) : HasLiftingProperty s i := by
  refine ⟨fun {u v} sq => ⟨⟨?_⟩⟩⟩
  have hsq (a : A) : ConcreteCategory.hom i (ConcreteCategory.hom u a) =
      ConcreteCategory.hom v (ConcreteCategory.hom s a) :=
    ConcreteCategory.congr_hom sq.w a
  let l : B → X := fun b => ConcreteCategory.hom u (Function.surjInv hs b)
  have hl : ConcreteCategory.hom i ∘ l = ConcreteCategory.hom v := funext fun b => by
    simp only [Function.comp_apply, l, hsq, Function.surjInv_eq hs b]
  have hmap : IsMap l := IsMap.of_comp_of_injective (ConcreteCategory.hom i).isMap hi
    (hl ▸ (ConcreteCategory.hom v).isMap)
  let lift : B ⟶ X := ConcreteCategory.ofHom (X := B) (Y := X) ⟨l, hmap⟩
  have hfac : lift ≫ i = v := by
    ext b
    exact congrFun hl b
  refine { l := lift, fac_left := hom_ext_of_inclusions hi ?_, fac_right := hfac }
  rw [Category.assoc, hfac, sq.w]

theorem subsingleton_liftStruct_of_inclusions {A B X Y : RDCpxDown.{u}} {s : A ⟶ B}
    {i : X ⟶ Y} (hi : inclusions i) {u : A ⟶ X} {v : B ⟶ Y} (sq : CommSq u s i v) :
    Subsingleton sq.LiftStruct :=
  ⟨fun l l' => CommSq.LiftStruct.ext
    (hom_ext_of_inclusions hi (l.fac_right.trans l'.fac_right.symm))⟩

end RDCpxDown

theorem IsLocalEmbedding.le_of_apply_le {P : OGP.{u}} {Q : OGP.{v}} {f : P → Q}
    (hf : IsLocalEmbedding f) {x y z : P} (hy : y ≤ x) (hz : z ≤ x) (h : f y ≤ f z) : y ≤ z := by
  have hmem {c : P} (hc : c ≤ x) : c ∈ closure ({x} : Set P) :=
    (Set.ext_iff.1 IsUpperSet.closure_singleton _).2 hc
  have hsp : (⟨z, hmem hz⟩ : closure ({x} : Set P)) ⤳ ⟨y, hmem hy⟩ :=
    (hf x).isInducing.specializes_iff.1 (IsUpperSet.specializes_iff_le.2 h)
  exact (IsUpperSet.specializes_iff_le (α := closure ({x} : Set P))).1 hsp

theorem IsMap.of_comp_of_isLocalEmbedding {P : OGP.{u}} {R : OGP.{v}} {S : OGP.{w}} {f : P → R}
    {g : R → S} (hg : IsMap g) (hle : IsLocalEmbedding g) (hf : Monotone f)
    (h : IsMap (g ∘ f)) : IsMap f := by
  refine ⟨IsUpperSet.isClosedMap_iff_fibration.2 fun x c hc => ?_,
    fun x n α => ⟨fun y hy => ?_, fun c hc => ?_⟩⟩
  · obtain ⟨x', hx'x, hx'⟩ := h.fibration (hg.monotone hc)
    exact ⟨x', hx'x, hle.injOn (hf hx'x) hc hx'⟩
  · have hyx : y ≤ x := LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ hy)
    have hy' : g (f y) ∈ g '' R.boundary (.Iic (f x)) n α := by
      rw [hg.image_boundary]
      exact (h.finalOn x n α).1 hy
    obtain ⟨w, hw, hwe⟩ := hy'
    rwa [hle.injOn (LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ hw)) (hf hyx) hwe] at hw
  · have hcx : c ≤ f x := LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ hc)
    have hgc : g c ∈ (S.boundary (.Iic (g (f x))) n α : Set S) := by
      rw [← hg.image_boundary]
      exact mem_image_of_mem g hc
    have he : (P.boundary (.Iic x) n α : Set P) ∩ f ⁻¹' Ici c =
        (P.boundary (.Iic x) n α : Set P) ∩ (g ∘ f) ⁻¹' Ici (g c) := by
      ext y
      refine and_congr_right fun hy => ⟨fun hcy => hg.monotone hcy, fun hcy =>
        hle.le_of_apply_le hcx (hf (LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ hy))) hcy⟩
    rw [he]
    exact (h.finalOn x n α).2 _ hgc

namespace RDCpxDown

variable {P Q : RDCpxDown.{u}}

def final : MorphismProperty RDCpxDown.{u} := fun _ _ f =>
  FinalOn (ConcreteCategory.hom f) Set.univ Set.univ

instance : final.{u}.IsMultiplicative where
  id_mem _ := finalOn_id _
  comp_mem _ g hf hg := hg.comp hf (ConcreteCategory.hom g).isMap.monotone

def pushforward (p : P ⟶ Q) : RDCpxDown.{u} :=
  ⟨OGP.pushforward (ConcreteCategory.hom p) (ConcreteCategory.hom p).isMap.monotone,
    (isLocalEmbedding_pushforwardLocal _ _).isRDC (isMorphism_pushforwardLocal _ _) Q.isRDC⟩

def pushforwardι (p : P ⟶ Q) : pushforward p ⟶ Q :=
  ConcreteCategory.ofHom (X := pushforward p) (Y := Q)
    ⟨pushforwardLocal (ConcreteCategory.hom p) (ConcreteCategory.hom p).isMap.monotone,
      (isMorphism_pushforwardLocal _ _).isMap_of_isRDC (pushforward p).isRDC Q.isRDC⟩

def toPushforward (p : P ⟶ Q) : P ⟶ pushforward p :=
  ConcreteCategory.ofHom (X := P) (Y := pushforward p)
    ⟨pushforwardFinal (ConcreteCategory.hom p) (ConcreteCategory.hom p).isMap.monotone,
      IsMap.of_comp_of_isLocalEmbedding (ConcreteCategory.hom (pushforwardι p)).isMap
        (isLocalEmbedding_pushforwardLocal _ (ConcreteCategory.hom p).isMap.monotone)
        (pushforwardFinal_monotone _ (ConcreteCategory.hom p).isMap.monotone)
        (ConcreteCategory.hom p).isMap⟩

@[reassoc (attr := simp)]
theorem toPushforward_pushforwardι (p : P ⟶ Q) : toPushforward p ≫ pushforwardι p = p := by
  ext x
  rfl

theorem final_toPushforward (p : P ⟶ Q) : final (toPushforward p) :=
  finalOn_pushforwardFinal (ConcreteCategory.hom p) (ConcreteCategory.hom p).isMap.monotone

theorem localEmbeddings_pushforwardι (p : P ⟶ Q) : localEmbeddings (pushforwardι p) :=
  isLocalEmbedding_pushforwardLocal (ConcreteCategory.hom p) (ConcreteCategory.hom p).isMap.monotone

theorem hasLiftingProperty_of_final_of_localEmbeddings {A B X Y : RDCpxDown.{u}}
    (s : A ⟶ B) (i : X ⟶ Y) (hs : final s) (hi : localEmbeddings i) : HasLiftingProperty s i := by
  refine ⟨fun {u v} sq => ⟨⟨?_⟩⟩⟩
  have hi' : IsLocalEmbedding (ConcreteCategory.hom i) := hi
  have hsq (a : A) : ConcreteCategory.hom i (ConcreteCategory.hom u a) =
      ConcreteCategory.hom v (ConcreteCategory.hom s a) :=
    ConcreteCategory.congr_hom sq.w a
  have hex (a : A) (b : B) (hb : b ≤ ConcreteCategory.hom s a) :
      ∃ c ≤ ConcreteCategory.hom u a, ConcreteCategory.hom i c = ConcreteCategory.hom v b :=
    IsUpperSet.isClosedMap_iff_fibration.1 hi'.isClosedMap
      ((hsq a).symm ▸ (ConcreteCategory.hom v).isMap.monotone hb)
  have hind (b : B) (a a' : A) (ha : b ≤ ConcreteCategory.hom s a)
      (ha' : b ≤ ConcreteCategory.hom s a') (c : X) (hc : c ≤ ConcreteCategory.hom u a)
      (hcb : ConcreteCategory.hom i c = ConcreteCategory.hom v b) :
      c ≤ ConcreteCategory.hom u a' := by
    have hz := IsUpperSet.isPreconnected_iff_reflTransGen.1 (hs.2 b trivial).2 a ⟨trivial, ha⟩
      a' ⟨trivial, ha'⟩
    clear ha'
    induction hz with
    | refl => exact hc
    | @tail a₁ a₂ _ hst ih =>
      obtain ⟨-, ⟨-, hb₂⟩, hle⟩ := hst
      rcases hle with hle | hle
      · exact ih.trans ((ConcreteCategory.hom u).isMap.monotone hle)
      · obtain ⟨c', hc', hc'b⟩ := hex a₂ b hb₂
        obtain rfl := hi'.injOn (hc'.trans ((ConcreteCategory.hom u).isMap.monotone hle)) ih
          (hc'b.trans hcb.symm)
        exact hc'
  choose a ha using fun b => (hs.2 b trivial).nonempty
  choose l hl hlb using fun b => hex (a b) b (ha b).2
  have hkey (b : B) (a' : A) (ha' : b ≤ ConcreteCategory.hom s a') :
      l b ≤ ConcreteCategory.hom u a' :=
    hind b (a b) a' (ha b).2 ha' (l b) (hl b) (hlb b)
  have hmono : Monotone l := fun b' b hb => by
    refine hi'.le_of_apply_le (hkey b' (a b) (hb.trans (ha b).2)) (hl b) ?_
    rw [hlb, hlb]
    exact (ConcreteCategory.hom v).isMap.monotone hb
  have hcomp : ConcreteCategory.hom i ∘ l = ConcreteCategory.hom v := funext hlb
  let lift : B ⟶ X := ConcreteCategory.ofHom (X := B) (Y := X)
    ⟨l, IsMap.of_comp_of_isLocalEmbedding (ConcreteCategory.hom i).isMap hi' hmono
      (hcomp ▸ (ConcreteCategory.hom v).isMap)⟩
  refine { l := lift, fac_left := ?_, fac_right := ?_ }
  · ext a'
    exact hi'.injOn (hkey _ a' le_rfl) le_rfl ((hlb _).trans (hsq a').symm)
  · ext b
    exact hlb b

theorem subsingleton_liftStruct_of_final_of_localEmbeddings {A B X Y : RDCpxDown.{u}}
    {s : A ⟶ B} {i : X ⟶ Y} (hs : final s) (hi : localEmbeddings i) {u : A ⟶ X} {v : B ⟶ Y}
    (sq : CommSq u s i v) : Subsingleton sq.LiftStruct := by
  refine ⟨fun l l' => CommSq.LiftStruct.ext ?_⟩
  have hi' : IsLocalEmbedding (ConcreteCategory.hom i) := hi
  ext b
  obtain ⟨a, -, hb⟩ := (hs.2 b trivial).nonempty
  have hle (m : sq.LiftStruct) : ConcreteCategory.hom m.l b ≤ ConcreteCategory.hom u a := by
    rw [← ConcreteCategory.congr_hom m.fac_left a]
    exact (ConcreteCategory.hom m.l).isMap.monotone hb
  have hv (m : sq.LiftStruct) :
      ConcreteCategory.hom i (ConcreteCategory.hom m.l b) = ConcreteCategory.hom v b :=
    ConcreteCategory.congr_hom m.fac_right b
  exact hi'.injOn (hle l) (hle l') ((hv l).trans (hv l').symm)

end RDCpxDown

end Atoms.Molecule.OGP
