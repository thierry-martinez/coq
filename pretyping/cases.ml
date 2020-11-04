(* Disable warning 40: Constructor or label name used out of scope.
   (Type-directed constructor and label selection.) *)
[@@@ocaml.warning "-40"]

(** {5 Compilation of pattern-matching } *)

(** {6 Pattern-matching errors } *)
type pattern_matching_error =
  | BadPattern of Names.constructor * EConstr.constr
  | BadConstructor of Names.constructor * Names.inductive
  | WrongNumargConstructor of Names.constructor * int
  | WrongNumargInductive of Names.inductive * int
  | UnusedClause of Glob_term.cases_pattern list
  | NonExhaustive of Glob_term.cases_pattern list
  | CannotInferPredicate of (EConstr.constr * EConstr.types) array

exception PatternMatchingError of
  Environ.env * Evd.evar_map * pattern_matching_error

let raise_pattern_matching_error ?loc (env,sigma,te) =
  Loc.raise ?loc (PatternMatchingError(env,sigma,te))

let error_bad_constructor ?loc env cstr ind =
  raise_pattern_matching_error ?loc
    (env, Evd.empty, BadConstructor (cstr,ind))

let error_wrong_numarg_constructor ?loc env c n =
  raise_pattern_matching_error ?loc
    (env, Evd.empty, WrongNumargConstructor(c,n))

let error_wrong_numarg_inductive ?loc env c n =
  raise_pattern_matching_error ?loc (env, Evd.empty, WrongNumargInductive(c,n))

let rec irrefutable env (pat : Glob_term.cases_pattern) =
  match DAst.get pat with
  | PatVar name -> true
  | PatCstr (cstr,args,_) ->
      let ind = Names.inductive_of_constructor cstr in
      let (_,mip) = Inductive.lookup_mind_specif env ind in
      let one_constr = Int.equal (Array.length mip.mind_user_lc) 1 in
      one_constr && List.for_all (irrefutable env) args

type compile_cases_typing_fun =
    Evardefine.type_constraint -> GlobEnv.t -> Evd.evar_map ->
      Glob_term.glob_constr -> Evd.evar_map * EConstr.unsafe_judgment

module type TypeS = sig
  type t
end

module Eq = struct
   type ('a, 'b) t = ('a, 'b) Util.eq = Refl : ('a, 'a) t

   let sym : type a b . (a, b) t -> (b, a) t = Util.sym

   let trans : type a b c . (a, b) t -> (b, c) t -> (a, c) t =
   fun Refl Refl -> Refl

   let cast : type a b . (a, b) t -> a -> b = fun Refl -> Fun.id

   let option : type a b . (a, b) t -> (a option, b option) t = fun Refl -> Refl

   let list : type a b . (a, b) t -> (a list, b list) t = fun Refl -> Refl

   let array : type a b . (a, b) t -> (a array, b array) t = fun Refl -> Refl

   let pair : type a b c d. (a, b) t -> (c, d) t -> (a * c, b * d) t =
   fun Refl Refl -> Refl

   let ( ^* ) = pair

   let arrow : type a b c d. (a, b) t -> (c, d) t -> (a -> c, b -> d) t =
   fun Refl Refl -> Refl

   let ( ^-> ) = arrow

   let endo eq = arrow eq eq
end

module Phantom (Type : TypeS) : sig
  type 'a t

  val eq : ('a t, Type.t) Eq.t

  val transtype : ('a t, 'b t) Eq.t
end = struct
  type 'a t = Type.t

  let eq = Eq.Refl

  let transtype = Eq.Refl
end

module Phantom2 (Type : TypeS) : sig
  type ('a, 'b) t

  val eq : (('a, 'b) t, Type.t) Eq.t
end = struct
  type ('a, 'b) t = Type.t

  let eq = Eq.Refl
end

module Phantom3 (Type : TypeS) : sig
  type ('a, 'b, 'c) t

  val eq : (('a, 'b, 'c) t, Type.t) Eq.t

  val transtype : (('a, 'b, 'c) t, ('d, 'e, 'f) t) Eq.t
end = struct
  type ('a, 'b, 'c) t = Type.t

  let eq = Eq.Refl

  let transtype = Eq.Refl
end

module type UnaryTypeS = sig
  type 'a t
end

module type BinaryTypeS = sig
  type ('a, 'b) t
end

module type TernaryTypeS = sig
  type ('a, 'b, 'c) t
end

module PhantomPoly (Type : UnaryTypeS) : sig
  type ('a, 'b) t

  val eq : (('a, 'b) t, 'a Type.t) Eq.t

  val transtype : (('a, 'b) t, ('a, 'c) t) Eq.t

  val morphism : ('a, 'b) Eq.t -> (('a, 'c) t, ('b, 'c) t) Eq.t
end = struct
  type ('a, 'b) t = 'a Type.t

  let eq = Eq.Refl

  let transtype = Eq.Refl

  let morphism : type a b c . (a, b) Eq.t -> ((a, c) t, (b, c) t) Eq.t =
    fun Refl -> Refl
end

module type Monad = sig
   type ('a, 'p) t

   module Ops : sig
     val return : 'a -> ('a, 'p) t

     val (let*) : ('a, 'p) t -> ('a -> ('b, 'p) t) -> ('b, 'p) t
   end
end

module MonadUtils (M : Monad) = struct
  let eq :
  type a b p q . (a, b) Eq.t -> (p, q) Eq.t -> ((a, p) M.t, (b, q) M.t) Eq.t =
  fun Refl Refl -> Refl

  let rec list_map : type a b p .
        (a -> (b, p) M.t) -> a list -> (b list, p) M.t =
  fun f l ->
    let open M.Ops in
    match l with
    | [] -> return []
    | h :: t ->
        let* h' = f h in
        let* t' = list_map f t in
        return (h' :: t')

  let option_map : type a b p .
        (a -> (b, p) M.t) -> a option -> (b option, p) M.t =
  fun f o ->
    let open M.Ops in
    match o with
    | None -> return None
    | Some x ->
        let* x' = f x in
        return (Some x')
end

module OptionMonad = struct
  module Self = struct
    type ('a, _) t = 'a option

    module Ops = struct
      let return x = Some x

      let (let*) = Option.bind
    end
  end

  include Self

  include MonadUtils (Self)
end

module Nat = struct
  (* Constructors Zero and Succ are never used:
     they are here for injectivity. *)

  type zero = Zero [@@ocaml.warning "-37"]

  type 'a succ = Succ [@@ocaml.warning "-37"]

  type 'a t =
    | O : zero t
    | S : 'a t -> 'a succ t

  let rec to_int : type a . ?add:int -> a t -> int  = fun ?(add = 0) a ->
    match a with
    | O -> add
    | S a -> to_int ~add:(add + 1) a

  type exists = Exists : 'a t -> exists

  let rec is_eq : type a b . a t -> b t -> (a, b) Eq.t option = fun n m ->
  match n, m with
  | O, O -> Some Refl
  | S n, S m ->
    begin match is_eq n m with
    | None -> None
    | Some Refl -> Some Refl
    end
  | _ -> None

  let of_int ?accu n =
    let rec aux : type a . a t -> int -> exists = fun accu n ->
      if n > 0 then
        aux (S accu) (pred n)
      else if n = 0 then
        Exists accu
      else
        assert false in
    match accu with
    | None -> aux O n
    | Some accu -> aux accu n

  type ('a, 'b, 'a_plus_b) plus =
    | Zero_l : (zero, 'a, 'a) plus
    | Succ_plus : ('a, 'b, 'c) plus -> ('a succ, 'b, 'c succ) plus

  type ('a, 'b) add =
    Exists : 'a_plus_b t * ('a, 'b, 'a_plus_b) plus -> ('a, 'b) add

  let rec add : type a b . a t -> b t -> (a, b) add = fun a b ->
    match a with
    | O -> Exists (b, Zero_l)
    | S a ->
        let Exists (c, a_plus_b) = add a b in
        Exists (S c, Succ_plus a_plus_b)

  let rec plus_succ : type a b a_plus_b .
        (a, b, a_plus_b) plus -> (a, b succ, a_plus_b succ) plus = fun plus ->
    match plus with
    | Zero_l -> Zero_l
    | Succ_plus plus -> Succ_plus (plus_succ plus)

  let rec zero_r : type a . a t -> (a, zero, a) plus = fun a ->
    match a with
    | O -> Zero_l
    | S a -> Succ_plus (zero_r a)

  let rec plus_commut : type a b sum .
        b t -> (a, b, sum) plus -> (b, a, sum) plus = fun b plus ->
    match plus with
    | Zero_l -> zero_r b
    | Succ_plus plus -> plus_succ (plus_commut b plus)
end

module Rank = struct
  type 'upper t =
    | O : _ t
    | S : 'a t -> 'a Nat.succ t
end

module Diff = struct
  type 'a t =
    Exists : ('x, 'y Nat.succ, 'a) Nat.plus -> 'a t

  let rec to_nat : type a b c . (a, b, c) Nat.plus -> a Nat.t = fun plus ->
    match plus with
    | Zero_l -> O
    | Succ_plus plus -> S (to_nat plus)

  let move_succ_left : type a b c .
    a Nat.t -> b Nat.t -> (a, b Nat.succ, c) Nat.plus ->
      (a Nat.succ, b, c) Nat.plus =
  fun a b plus ->
    let Succ_plus plus' = Nat.plus_commut (S b) plus in
    Nat.plus_commut (S a) (Nat.plus_succ plus')
end

module Vector = struct
  type ('a, 'length) t =
    | [] : ('a, Nat.zero) t
    | (::) : 'a * ('a, 'length) t -> ('a, 'length Nat.succ) t

  type 'a exists = Exists : ('a, 'length) t -> 'a exists

  let rec make : type length . length Nat.t -> 'a -> ('a, length) t = fun n x ->
    match n with
    | O -> []
    | S n -> x :: make n x

  let rec of_list : type a . a list -> a exists = fun l ->
    match l with
    | [] -> Exists []
    | hd :: tl ->
        let Exists tl = of_list tl in
        Exists (hd :: tl)

  let rec of_list_of_length : type a length . a list -> length Nat.t ->
    (a, length) t option = fun l len ->
    let open OptionMonad.Ops in
    match l, len with
    | [], Nat.O -> return []
    | hd :: tl, Nat.S len ->
        let* tl = of_list_of_length tl len in
        return (hd :: tl)
    | _ -> None

  let rec of_list_map : type a b . (a -> b) -> a list -> b exists = fun f l ->
    match l with
    | [] -> Exists []
    | hd :: tl ->
        let Exists tl = of_list_map f tl in
        Exists (f hd :: tl)

  let rec to_list : type a length . (a, length) t -> a list = fun l ->
    match l with
    | [] -> []
    | hd :: tl -> hd :: to_list tl

  let rec length : type a length . (a, length) t -> length Nat.t = fun l ->
    match l with
    | [] -> O
    | _hd :: tl -> S (length tl)

  let rec find : type length . ('a -> bool) -> ('a, length) t -> 'a = fun p l ->
    match l with
    | [] -> raise Not_found
    | hd :: tl ->
        if p hd then hd
        else find p tl

  let rec iter : type length . ('a -> unit) -> ('a, length) t -> unit =
  fun f l ->
    match l with
    | [] -> ()
    | hd :: tl ->
        f hd;
        iter f tl

  let rec map : type length . ('a -> 'b) -> ('a, length) t -> ('b, length) t =
  fun f l ->
    match l with
    | [] -> []
    | hd :: tl -> f hd :: map f tl

  let rec map2 : type length .
    ('a -> 'b -> 'c) -> ('a, length) t -> ('b, length) t -> ('c, length) t =
  fun f l1 l2 ->
    match l1, l2 with
    | [], [] -> []
    | hd1 :: tl1, hd2 :: tl2 -> f hd1 hd2 :: map2 f tl1 tl2

  let rec map_split : type length .
    ('a -> 'b * 'c) -> ('a, length) t -> ('b, length) t * ('c, length) t =
  fun f l ->
    match l with
    | [] -> [], []
    | hd :: tl ->
        let hd0, hd1 = f hd in
        let tl0, tl1 = map_split f tl in
        hd0 :: tl0, hd1 :: tl1

  let rec map_rev_append : type l l0 l1 .
        ('a -> 'b) -> ('a, l0) t -> ('b, l1) t -> (l0, l1, l) Nat.plus ->
        ('b, l) t = fun f l0 l1 plus ->
    match l0, plus with
    | [], Zero_l -> l1
    | hd :: tl, Succ_plus plus ->
        map_rev_append f tl (f hd :: l1) (Nat.plus_succ plus)

  let rev : type l . ('a, l) t -> ('a, l) t = fun l ->
    map_rev_append Fun.id l [] (Nat.zero_r (length l))

  let append : type l l0 l1 .
      ('a, l0) t -> ('b, l1) t -> (l0, l1, l) Nat.plus -> ('a, l) t =
  fun l0 l1 plus ->
    map_rev_append Fun.id (rev l0) l1 plus

  let rec mapi_aux :
  type i l l' . i Nat.t -> l' Nat.t -> (i, l', l) Nat.plus ->
    (l Diff.t -> 'a -> 'b) -> ('a, l') t -> ('b, l') t =
  fun i l' diff f l ->
    match l, l' with
    | [], O -> []
    | hd :: tl, S l' ->
       f (Exists diff) hd :: mapi_aux (S i) l'
         (Diff.move_succ_left i l' diff) f tl

  let mapi : type l . (l Diff.t -> 'a -> 'b) -> ('a, l) t -> ('b, l) t =
  fun f l ->
    mapi_aux O (length l) Zero_l f l

  let rec get_aux : type i l l' .
    (i, l' Nat.succ, l) Nat.plus -> ('a, l) t -> 'a =
  fun plus l ->
    match plus, l with
    | Zero_l, hd :: _ -> hd
    | Succ_plus plus, _ :: tl ->
        get_aux plus tl
    | _ -> .

  module Ops = struct
    let (.%()) (type l) (l : ('a, l) t) (Exists plus : l Diff.t) : 'a =
      get_aux plus l
  end

  let rec for_all : type length . ('a -> bool) -> ('a, length) t -> bool =
  fun p l ->
    match l with
    | [] -> true
    | hd :: tl -> p hd && for_all p tl

  module UseMonad (M : Monad) = struct
    let rec map : type length a b p .
          (a -> (b, p) M.t) -> (a, length) t ->
            ((b, length) t, p) M.t =
    fun f v ->
      let open M.Ops in
      match v with
      | [] -> return []
      | h :: t ->
          let* h' = f h in
          let* t' = map f t in
          return (h' :: t')
  end
end

module Env = struct
  include Phantom (struct type t = Environ.env end)

  let pair :
    type a b c d . (a t, b t) Eq.t -> (c t, d t) Eq.t ->
      ((a * c) t, (b * d) t) Eq.t = fun _ _ -> transtype

  let zero_l : type env . ((Nat.zero * env) t, env t) Eq.t = transtype

  let zero_r : type env . ((env * Nat.zero) t, env t) Eq.t = transtype

  let succ : type a . ((a * Nat.zero Nat.succ) t, a Nat.succ t) Eq.t = transtype

  let assoc : type a b c . (((a * b) * c) t, (a * (b * c)) t) Eq.t = transtype

  let commut : type a b . ((a * b) t, (b * a) t) Eq.t = transtype

  let morphism : type a b c d .
    (a t, b t) Eq.t -> (c t, d t) Eq.t -> ((a * c) t, (b * d) t) Eq.t =
  fun _ _ -> transtype

  let plus :
    type a b . (a, b, 'c) Nat.plus -> ((a * b) t, 'c t) Eq.t =
  fun _ -> transtype
end

module Height = struct
  include Phantom (struct type t = int end)

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) : (a t, b t) Eq.t =
    transtype

  let zero : Nat.zero t = Eq.cast (Eq.sym eq) 0

  let one : (Nat.zero Nat.succ) t = Eq.cast (Eq.sym eq) 1

  let add (type a b) (a : a t) (b : b t) : (a * b) t =
    Eq.cast (Eq.sym eq) (Eq.cast eq a + Eq.cast eq b)

  let succ (type a) (a : a t) : (a Nat.succ) t =
    Eq.cast (Eq.sym eq) (succ (Eq.cast eq a))

  let of_nat : type n . n Nat.t -> n t = fun n ->
    Eq.cast (Eq.sym eq) (Nat.to_int n)

  type 'n to_nat = Exists : 'm Nat.t * ('m Env.t, 'n Env.t) Eq.t -> 'n to_nat

  let to_nat : type n . n t -> n to_nat = fun n ->
    let n = Eq.cast eq n in
    let Exists m = Nat.of_int n in
    Exists (m, Env.transtype)

  let to_int n =
    Eq.cast eq n

  type ('a, 'b) diff = Exists : {
      diff : 'diff t;
      plus : (('diff * 'b) Env.t, 'a Env.t) Eq.t;
    } -> ('a, 'b) diff

  let diff_zero : type a . (a, a) diff = Exists {
      diff = zero;
      plus = Env.zero_l;
    }

  let diff_add (type a b c) (a : a t) (Exists b : (b, c) diff) :
      (a * b, c) diff = Exists {
      diff = add a b.diff;
      plus = Eq.trans Env.assoc (Env.morphism Refl b.plus);
    }

  let sub (type a b) (a : a t) (b : b t) : (a, b) diff =
    Exists {
      diff = Eq.(cast (sym (eq ^-> eq ^-> eq))) (-) a b;
      plus = Env.transtype;
  }
end

module Index = struct
  include Phantom (struct type t = int end)

  let zero (type n) () : n Nat.succ t =
    Eq.(cast (sym eq)) 0

  let succ (type n) (n : n t) : n Nat.succ t =
    Eq.(cast (sym (eq ^-> eq))) succ n
end

module Tuple = struct
  include PhantomPoly (struct type 'a t = 'a array end)

  module Ops = struct
    let (.%()) (type length) (tuple : ('a, length) t) (index : length Index.t) =
      Array.unsafe_get (Eq.cast eq tuple) (Eq.cast Index.eq index)

    let (.%()<-) (type length) (tuple : ('a, length) t)
        (index : length Index.t) (value : 'a) =
      Array.unsafe_set (Eq.cast eq tuple) (Eq.cast Index.eq index) value
  end

  let length (type length) (t : ('a, length) t) : length Height.t =
    Eq.cast (Eq.sym (Eq.arrow eq Height.eq)) Array.length t

  let make (l : 'length Height.t) (default : 'a) : ('a, 'length) t =
    Eq.cast Eq.(sym (Height.eq ^-> Refl ^-> eq)) Array.make l default

  let init (l : 'length Height.t) (f : 'length Index.t -> 'a) :
    ('a, 'length) t =
    Eq.(cast (sym (Height.eq ^-> (Index.eq ^-> Refl) ^-> eq))) Array.init l f

  let iter (t : ('a, 'length) t) (f : 'length Index.t -> unit) : unit =
    for i = 0 to Array.length (Eq.cast eq t) - 1 do
      f (Eq.cast (Eq.sym Index.eq) i)
    done

  let map (f : ('a -> 'b)) (t : ('a, 'length) t) : ('b, 'length) t =
    Eq.(cast (sym (Refl ^-> eq ^-> eq))) Array.map f t

  type 'a exists = Exists : ('a, 'length) t -> 'a exists
end

module type Type = sig
  type t
end

module StateMonad = struct
  module Self = struct
    type ('a, 'state) t = 'state -> 'state * 'a

    module Ops = struct
     let return x sigma =
       (sigma, x)

     let (let*) x f sigma =
       let (sigma, y) = x sigma in
       f y sigma
    end
  end

  include Self

  let get : type state . (state, state) t =
    fun state -> (state, state)

  let set : type state . state -> (unit, state) t =
    fun new_state state -> (new_state, ())

  let run : type state a . state -> (a, state) t -> state * a =
    fun state m -> m state

  include MonadUtils (Self)

  let array_init : type a p . int -> (int -> (a, p) t) -> (a array, p) t =
  fun len f state ->
     let state_ref = ref state in
     let result =
       Array.init len (fun i ->
         let state, result = f i !state_ref in
         state_ref := state;
         result) in
     !state_ref, result

  let array_map : type a b p .
        (a -> (b, p) t) -> a array -> (b array, p) t =
  fun f a ->
    array_init (Array.length a) (fun i -> f (Array.unsafe_get a i))

  let array_mapi : type a b p .
        (int -> a -> (b, p) t) -> a array -> (b array, p) t =
  fun f a ->
    array_init (Array.length a) (fun i -> f i (Array.unsafe_get a i))

  let tuple_map : type a b p l .
        (a -> (b, p) t) -> (a, l) Tuple.t -> ((b, l) Tuple.t, p) t =
  fun f t ->
    Eq.(cast (sym (Tuple.eq ^-> eq Tuple.eq Refl)))
      (array_map f) t

  let tuple_mapi : type a b p l .
        (l Index.t -> a -> (b, p) t) -> (a, l) Tuple.t ->
          ((b, l) Tuple.t, p) t =
  fun f t ->
    Eq.(cast (sym
        ((Index.eq ^-> Refl ^-> Refl) ^-> Tuple.eq ^-> eq Tuple.eq Refl)))
      array_mapi f t
end

module InductiveDef = struct
  include Phantom (struct type t = Names.inductive end)

  let equal (type ind ind') (ind : ind t) (ind' : ind' t) :
      (ind t, ind' t) Eq.t option =
    if Names.eq_ind (Eq.cast eq ind) (Eq.cast eq ind') then
      Some transtype
    else
      None
end

module type ConcreteTermS = sig
  type t

  type rel_declaration = (t, t) Context.Rel.Declaration.pt

  type rel_context = (t, t) Context.Rel.pt

  val liftn : int -> int -> t -> t

  val mkRel : int -> t

  val mkProp : t

  val mkInd : Names.inductive -> t

  val mkApp : t * t array -> t

  val it_mkLambda_or_LetIn : t -> rel_context -> t
end

module type ConcreteLiftS = sig
  module Phantom : TernaryTypeS

  module Concrete : TypeS

  val unsafe_map :
      (Concrete.t -> Concrete.t) ->
        ('a, 'p, 'q) Phantom.t -> ('b, 'p, 'q) Phantom.t

  val liftn : int -> int -> Concrete.t -> Concrete.t
end

module type LiftS = sig
  type ('env, 'p, 'q) t

  val liftn : 'n Height.t -> 'm Height.t -> ('env * 'm, 'p, 'q) t ->
      (('env * 'n) * 'm, 'p, 'q) t

  val lift : 'n Height.t -> ('env, 'p, 'q) t -> ('env * 'n, 'p, 'q) t
end

module Lift (X : ConcreteLiftS) :
    LiftS with type ('env, 'p, 'q) t := ('env, 'p, 'q) X.Phantom.t = struct
  let liftn (type env n m)
      (n : n Height.t) (m : m Height.t) (term : (env * m, 'p, 'q) X.Phantom.t) :
      ((env * n) * m, 'p, 'q) X.Phantom.t =
    X.unsafe_map
      (X.liftn (Eq.cast Height.eq n) (succ (Eq.cast Height.eq m)))
      term

  let lift (type env n m) (n : n Height.t) (term : (env, 'p, 'q) X.Phantom.t) :
      (env * n, 'p, 'q) X.Phantom.t =
    X.unsafe_map (X.liftn (Eq.cast Height.eq n) 1) term
end

module type AbstractTermS = sig
  module Concrete : ConcreteTermS

  type 'a t

  val eq : ('a t, Concrete.t) Eq.t

  val morphism : ('a Env.t, 'b Env.t) Eq.t -> ('a t, 'b t) Eq.t

  include LiftS with type ('env, 'p, 'q) t := 'env t

  val mkRel : 'a Index.t -> 'a t

  val mkProp : unit -> 'a t

  val mkInd : 'ind InductiveDef.t -> 'env t

  val mkApp : 'env t -> 'env t array -> 'env t
end

module AbstractTerm (X : ConcreteTermS) :
    AbstractTermS with module Concrete = X = struct
  module Concrete = X

  include Phantom (struct type t = X.t end)

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) :
      (a t, b t) Eq.t =
    transtype

  include Lift (struct
    module Phantom = struct type nonrec ('a, 'p, 'q) t = 'a t end
    module Concrete = X
    let unsafe_map f =
      Eq.(cast (sym (eq ^-> eq))) f
    let liftn = X.liftn
  end)

  let mkRel (i : 'env Index.t) : 'env t =
    Eq.(cast (sym (Index.eq ^-> eq))) (fun i -> X.mkRel (succ i)) i

  let mkProp () : 'env t = Eq.cast (Eq.sym eq) X.mkProp

  let mkInd (ind : 'ind InductiveDef.t) : 'env t =
    Eq.cast (Eq.sym (Eq.arrow InductiveDef.eq eq)) X.mkInd ind

  let mkApp (f : 'env t) (args : 'env t array) : 'env t =
    Eq.cast (Eq.sym eq) (X.mkApp (Eq.cast eq f, Eq.cast (Eq.array eq) args))
end

module Term = struct
  include AbstractTerm (struct
    include Constr

    include Term
  end)
end

module ETerm = struct
  include AbstractTerm (struct
    include EConstr

    let liftn = Vars.liftn
  end)

  let whd_all (type env) (env : env Env.t) (sigma : Evd.evar_map)
      (term : env t) =
    Eq.cast (Eq.sym eq)
      (Reductionops.whd_all (Eq.cast Env.eq env) sigma
         (Eq.cast eq term))

  let substnl (type env n length) (substl : (env t, length) Vector.t)
      (n : n Height.t) (t : ((env * length) * n) t) : (env * n) t =
    Eq.(cast (sym (Eq.list eq ^-> Height.eq ^-> eq ^-> eq)))
      EConstr.Vars.substnl (Vector.to_list substl) n t

  let substl (type env length) (substl : (env t, length) Vector.t)
      (t : (env * length) t) : env t =
    Eq.(cast (sym (Eq.list eq ^-> eq ^-> eq)))
      EConstr.Vars.substl (Vector.to_list substl) t

  let subst1 (type env) (s : env t) (t : (env * Nat.zero Nat.succ) t) : env t =
    substl [s] t

  let noccur_between (sigma : Evd.evar_map) n m (term : 'env t) : bool =
    EConstr.Vars.noccur_between sigma n m (Eq.cast eq term)

  let of_term (t : 'env Term.t) : 'env t =
    Eq.(cast (sym (Term.eq ^-> eq))) EConstr.of_constr t
end

module EvarMapMonad = struct
  include StateMonad

  type 'a t = ('a, Evd.evar_map) StateMonad.t

  let new_type_evar (env : 'env Env.t) rigid : ('env ETerm.t * Sorts.t) t =
  fun sigma ->
    Eq.cast (Eq.pair Refl (Eq.pair (Eq.sym ETerm.eq) Refl))
      (Evarutil.new_type_evar (Eq.cast Env.eq env) sigma rigid)

  let new_evar (env : 'env Env.t) (ty : 'env ETerm.t) : 'env ETerm.t t =
  fun sigma ->
    Eq.cast (Eq.pair Refl (Eq.sym ETerm.eq))
      (Evarutil.new_evar (Eq.cast Env.eq env) sigma (Eq.cast ETerm.eq ty))
end

module AbstractJudgment (X : AbstractTermS) = struct
  type concrete = (X.Concrete.t, X.Concrete.t) Environ.punsafe_judgment

  include Phantom (struct
    type t = concrete
  end)

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) :
      a t -> b t =
    Eq.cast (Eq.arrow (Eq.sym eq) (Eq.sym eq)) Fun.id

  let uj_val (j : 'env t) : 'env X.t =
    Eq.cast (Eq.sym (Eq.arrow eq X.eq)) (fun j -> j.uj_val) j

  let uj_type (j : 'env t) : 'env X.t =
    Eq.cast (Eq.sym (Eq.arrow eq X.eq)) (fun j -> j.uj_type) j

  let make (type env) (uj_val : env X.t) (uj_type : env X.t) : env t =
    Eq.cast (Eq.sym Eq.(X.eq ^-> X.eq ^-> eq))
      Environ.make_judge uj_val uj_type

  include Lift (struct
    module Phantom = struct type nonrec ('a, 'p, 'q) t = 'a t end
    module Concrete = struct type t = concrete end
    let unsafe_map f =
      Eq.(cast (sym (eq ^-> eq))) f
    let liftn n m decl =
      Environ.on_judgment (X.Concrete.liftn n m) decl
  end)
end

module JudgmentMap (X0 : AbstractTermS) (X1 : AbstractTermS) = struct
  module J0 = AbstractJudgment (X0)
  module J1 = AbstractJudgment (X1)

  let map (type a b) (f : a X0.t -> b X1.t) (j : a J0.t) : b J1.t =
    match Eq.cast J0.eq j with
    | { uj_val; uj_type } ->
        Eq.cast (Eq.sym J1.eq) {
          uj_val = Eq.(cast (X0.eq ^-> X1.eq)) f uj_val;
          uj_type = Eq.(cast (X0.eq ^-> X1.eq)) f uj_type; }
end

module EJudgment = struct
  include AbstractJudgment (ETerm)

  include JudgmentMap (ETerm) (ETerm)

  let inh_conv_coerce_to (type env) ~program_mode ~resolve_tc (env : env Env.t)
      (judgment : env t) (t : env ETerm.t) :
      (env t  * Coercion.coercion_trace option) EvarMapMonad.t =
    Eq.cast (EvarMapMonad.eq (Eq.pair (Eq.sym eq) Refl) Refl) (fun sigma ->
      let sigma, result, trace =
        Coercion.inh_conv_coerce_to ~program_mode resolve_tc
          (Eq.cast Env.eq env)
          sigma (Eq.cast eq judgment) (Eq.cast ETerm.eq t) in
       (sigma, (result, trace)))
end

module AbstractDeclaration (X : AbstractTermS) = struct
  module Judgment = AbstractJudgment (X)

  type concrete = X.Concrete.rel_declaration

  include Phantom (struct
    type t = concrete
  end)

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) : (a t, b t) Eq.t =
    transtype

  let assum (type env) as_name (ty : env X.t) : env t =
    Eq.cast (Eq.sym eq) (LocalAssum (as_name, Eq.cast X.eq ty))

  let local_def (type env) (as_name : Names.Name.t Context.binder_annot)
      (judgment : env Judgment.t) : env t =
    let uj_val = Eq.cast X.eq (Judgment.uj_val judgment) in
    let uj_type = Eq.cast X.eq (Judgment.uj_type judgment) in
    Eq.cast (Eq.sym eq) (LocalDef (as_name, uj_val, uj_type))

  let get_type (type env) (d : env t) : env X.t =
    Eq.(cast (sym (eq ^-> X.eq))) Context.Rel.Declaration.get_type d

  include Lift (struct
    module Phantom = struct type nonrec ('a, 'p, 'q) t = 'a t end
    module Concrete = struct type t = concrete end
    let unsafe_map f =
      Eq.(cast (sym (eq ^-> eq))) f
    let liftn n m decl =
      Context.Rel.Declaration.map_constr (X.Concrete.liftn n m) decl
  end)

  let set_name name decl =
    Eq.(cast (sym (Refl ^-> eq ^-> eq))) Context.Rel.Declaration.set_name
      name decl
end

module DeclarationMap (X0 : AbstractTermS) (X1 : AbstractTermS) = struct
  module D0 = AbstractDeclaration (X0)
  module D1 = AbstractDeclaration (X1)

  let map (type a b) (f : a X0.t -> b X1.t) (d : a D0.t) : b D1.t =
    Eq.(cast (sym ((X0.eq ^-> X1.eq) ^-> D0.eq ^-> D1.eq)))
      Context.Rel.Declaration.map_constr_het f d
end

module EDeclaration = struct
  include AbstractDeclaration (ETerm)

  let of_declaration d =
    let module Map = DeclarationMap (Term) (ETerm) in
    Map.map ETerm.of_term d
end

module AbstractRelContext (X : AbstractTermS) = struct
  module Declaration = AbstractDeclaration (X)

  type ('env, 'length) t =
    | [] : ('env, Nat.zero) t
    | (::) : ('env * 'length) Declaration.t * ('env, 'length) t ->
        ('env, 'length Nat.succ) t

  let rec morphism : type a b length .
        (a Env.t, b Env.t) Eq.t -> (a, length) t -> (b, length) t =
  fun eq context ->
    match context with
    | [] -> []
    | hd :: tl ->
        Eq.cast (Declaration.morphism (Env.morphism eq Refl)) hd ::
        morphism eq tl

  let rec push : type outer length_inner length_outer length .
      (outer * length_outer, length_inner) t ->
      (outer, length_outer) t ->
      (length_inner, length_outer, length) Nat.plus ->
      (outer, length) t =
  fun inner_context outer_context plus ->
    match inner_context, plus with
    | [], Zero_l -> outer_context
    | hd :: tl, Succ_plus plus ->
        Eq.cast (Declaration.morphism (Eq.trans Env.assoc (Env.morphism Refl
          (Eq.trans Env.commut (Env.plus plus))))) hd ::
        push tl outer_context plus

  let rec length : type env length . (env, length) t -> length Nat.t =
  fun v ->
    match v with
    | [] -> O
    | _hd :: tl -> S (length tl)

  type 'env exists = Exists : ('env, 'length) t -> 'env exists

  type concrete = X.Concrete.rel_context

  type ('env, 'height) with_height =
      Exists : ('env, 'length) t * ('length Env.t, 'height Env.t) Eq.t ->
        ('env, 'height) with_height

  let rec of_concrete : type env . concrete -> env exists =
  fun context ->
    match context with
    | [] -> Exists []
    | hd :: tl ->
        let Exists tl = of_concrete tl in
        Exists (Eq.cast (Eq.sym Declaration.eq) hd :: tl)

  let rec to_concrete : type env length . (env, length) t -> concrete =
  fun context ->
    match context with
    | [] -> []
    | hd :: tl -> Eq.cast Declaration.eq hd :: to_concrete tl

  let rec liftn_aux : type env n m length .
    n Height.t -> m Height.t -> (env * m, length) t ->
      ((env * n) * m, length) t * length Height.t =
  fun n m context ->
    match context with
    | [] -> [], Height.zero
    | hd :: tl ->
        let tl, l = liftn_aux n m tl in
        Eq.cast (Eq.sym (Declaration.morphism Env.assoc))
          (Declaration.liftn n (Height.add m l)
            (Eq.cast (Declaration.morphism Env.assoc) hd)) :: tl, Height.succ l

  let liftn n m context =
    fst (liftn_aux n m context)

  let lift (type env length n) (n : n Height.t) (context : (env, length) t) :
      (env * n, length) t =
    morphism Env.zero_r
      (liftn n Height.zero (morphism (Eq.sym Env.zero_r) context))

  let untyped_liftn n m context =
    let add decl (new_context, m) =
      new_context |> Context.Rel.add
        (Context.Rel.Declaration.map_constr (X.Concrete.liftn n m) decl),
      succ m in
    let new_context, _m =
      Context.Rel.fold_outside add context ~init:(Context.Rel.empty, m) in
    new_context

  let it_mkLambda_or_LetIn (type env length)
      (t : (env * length) X.t) (context : (env, length) t) : env X.t =
    Eq.(cast (sym (X.eq ^-> Refl ^-> X.eq)))
      X.Concrete.it_mkLambda_or_LetIn t (to_concrete context)

  module Judgment = Declaration.Judgment

  let rec to_rel_vector : type env length .
      (env, length) t ->
        ((env * length) Judgment.t, length) Vector.t =
  fun context ->
    match context with
    | [] -> []
    | hd :: tl ->
        let tl = to_rel_vector tl in
        Judgment.morphism (Eq.trans (Eq.trans (Eq.sym Env.succ) Env.assoc)
          (Env.morphism Refl Env.succ))
        (Judgment.make (X.mkRel (Index.zero ()))
          (Eq.cast (X.morphism Env.succ)
             (X.lift Height.one (Declaration.get_type hd)))) ::
        Vector.map
          (fun j -> Judgment.morphism (Eq.trans Env.assoc (Env.morphism Refl
             Env.succ)) (Judgment.lift Height.one j)) tl

  let rec set_names : type env length .
    (Names.Name.t, length) Vector.t -> (env, length) t ->
      (env, length) t =
  fun names context ->
    match names, context with
    | [], [] -> []
    | name :: names, hd :: tl ->
        Declaration.set_name name hd :: set_names names tl
end

module RelContextMap (X0 : AbstractTermS) (X1 : AbstractTermS) = struct
  module C0 = AbstractRelContext (X0)
  module C1 = AbstractRelContext (X1)

  type map = {
      f : 'height . 'height C0.Declaration.t -> 'height C1.Declaration.t;
    }

  let rec map : type env length .
    map -> (env, length) C0.t -> (env, length) C1.t =
  fun f c ->
    match c with
    | [] -> []
    | hd :: tl -> f.f hd :: map f tl
end

module RelContext = AbstractRelContext (Term)

module ERelContext = struct
  include AbstractRelContext (ETerm)

  let of_rel_context c =
    let module Map = RelContextMap (Term) (ETerm) in
    Map.map { f = EDeclaration.of_declaration } c
end


module GlobalEnv = struct
  include Phantom (struct type t = GlobEnv.t end)

  let env glob_env =
    Eq.cast (Eq.sym Env.eq) (GlobEnv.env (Eq.cast eq glob_env))

  let push_rel (type env) ~hypnaming
      (sigma : Evd.evar_map) (d : env EDeclaration.t)
      (glob_env : env t) : env EDeclaration.t * (env * Nat.zero Nat.succ) t =
    Eq.cast (Eq.pair (Eq.sym EDeclaration.eq) (Eq.sym eq))
      (GlobEnv.push_rel ~hypnaming sigma (Eq.cast EDeclaration.eq d)
         (Eq.cast eq glob_env))

  let push_rel_context (type env) (type height) ~hypnaming
      (sigma : Evd.evar_map) (context : (env, height) ERelContext.t)
      (glob_env : env t) : (env, height) ERelContext.t * (env * height) t =
    let context', env =
      GlobEnv.push_rel_context ~hypnaming sigma
         (ERelContext.to_concrete context) (Eq.cast eq glob_env) in
    let Exists context' = ERelContext.of_concrete context' in
    match Nat.is_eq (ERelContext.length context)
        (ERelContext.length context') with
    | None -> assert false
    | Some Refl -> context', Eq.cast (Eq.sym eq) env

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) :
      (a t, b t) Eq.t =
    transtype
end

module InductiveSpecif = struct
  include Phantom2 (struct type t = Inductive.mind_specif end)

  let lookup (type env ind) (env : env Env.t) (ind : ind InductiveDef.t) :
      (env, ind) t =
    Eq.cast (Eq.sym (Eq.arrow Env.eq (Eq.arrow InductiveDef.eq eq)))
      Inductive.lookup_mind_specif env ind

  let constructors (type env ind) (specif : (env, ind) t) :
      (env Term.t, ind) Tuple.t =
    Eq.cast (Eq.trans (Eq.array (Eq.sym (Term.eq))) (Eq.sym Tuple.eq))
      (snd (Eq.cast eq specif)).mind_user_lc
end

module AnnotatedVector = struct
  module Self (S : BinaryTypeS) = struct
    type ('env, 'length, 'annot, 'end_annot) section =
      | [] : ('env, Nat.zero, 'end_annot, 'end_annot) section
      | (::) :
          ('env, 'head) S.t * ('env, 'length, 'tail, 'end_annot) section ->
            ('env, 'length Nat.succ, 'head * 'tail, 'end_annot) section

    type ('env, 'length, 'annot) t = ('env, 'length, 'annot, unit) section

    type ('a, 'b) map = {
        f : 'annot . ('a, 'annot) S.t -> 'b;
      }

    let rec length : type env length annot end_annot .
          (env, length, annot, end_annot) section -> length Nat.t =
    fun v ->
      match v with
      | [] -> O
      | _ :: tl -> S (length tl)

    let rec to_vector : type a b length annot end_annot .
          (a, b) map -> (a, length, annot, end_annot) section ->
          (b, length) Vector.t =
    fun f v ->
      match v with
      | [] -> []
      | hd :: tl -> f.f hd :: to_vector f tl
  end

  module Map (S0 : BinaryTypeS) (S1 : BinaryTypeS) = struct
    module V0 = Self (S0)

    module V1 = Self (S1)

    type ('a, 'b) map =
        { f : 'annot .
            ('a, 'annot) S0.t -> ('b, 'annot) S1.t }

    let rec map_append : type a b annot0 annot1 annot2 length0 length1 length2 .
          (a, b) map -> (a, length0, annot0, annot1) V0.section ->
            (b, length1, annot1, annot2) V1.section ->
            (length0, length1, length2) Nat.plus ->
            (b, length2, annot0, annot2) V1.section =
    fun f v b plus ->
      match v, plus with
      | [], Nat.Zero_l -> b
      | hd :: tl, Nat.Succ_plus plus ->
          f.f hd :: map_append f tl b plus

    let map f v = map_append f v [] (Nat.zero_r (V0.length v))
  end

  module Make (S : BinaryTypeS) = struct
    include Self (S)

    include Map (S) (S)

    let append v0 v1 = map_append { f = Fun.id } v0 v1
  end
end

module Constructor = struct
  include Phantom (struct type t = Names.constructor end)

  type exists = Exists : 'ind t -> exists

  let of_constructor (cstr : Names.constructor) : exists =
    Exists (Eq.cast (Eq.sym eq) cstr)

  let inductive (cstr : 'ind t) : 'ind InductiveDef.t =
    Eq.cast (Eq.sym (Eq.arrow eq InductiveDef.eq))
      Names.inductive_of_constructor cstr

  let index (cstr : 'ind t) : 'ind Index.t =
    Eq.cast (Eq.sym (Eq.arrow eq Index.eq))
      (fun c -> pred (Names.index_of_constructor c)) cstr

  let make (ind : 'ind InductiveDef.t) (i : 'ind Index.t) : 'ind t =
    Eq.(cast (sym (InductiveDef.eq ^-> Index.eq ^-> eq)))
      Names.ith_constructor_of_inductive ind i

  let error_bad ?loc env cstr ind =
    raise_pattern_matching_error ?loc
      (Eq.cast Env.eq env, Evd.empty,
        BadConstructor (Eq.cast eq cstr, Eq.cast InductiveDef.eq ind))

  let error_wrong_numarg ?loc env c n =
    raise_pattern_matching_error ?loc
      (Eq.cast Env.eq env, Evd.empty, WrongNumargConstructor(Eq.cast eq c, n))
end

module InductiveFamily = struct
  type ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t = {
      def : 'ind InductiveDef.t Univ.puniverses;
      params : ('env Term.t, 'params) Vector.t;
      nrealargs : 'nrealargs Nat.t;
      nrealdecls : 'nrealdecls Nat.t;
    }

  type ('env, 'ind) exists =
      Exists :
        ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t -> ('env, 'ind) exists

  let of_concrete (env : 'env Env.t) (indf : Inductiveops.inductive_family) :
      ('env, 'ind) exists =
    let (ind, univ), params = Inductiveops.dest_ind_family indf in
    let Exists params =
      Vector.of_list (Eq.(cast (list (sym Term.eq))) params) in
    let def = Eq.cast (Eq.sym InductiveDef.eq) ind in
    let oib =
      snd (Eq.cast InductiveSpecif.eq (InductiveSpecif.lookup env def)) in
    let Exists nrealargs = Nat.of_int (oib.mind_nrealargs) in
    let Exists nrealdecls = Nat.of_int (oib.mind_nrealdecls) in
    Exists {
      def = (def, univ); params;
      nrealargs;
      nrealdecls }

  let to_concrete (indf : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t) :
      Inductiveops.inductive_family =
    let ind, univ = indf.def in
    let params = Eq.(cast (list Term.eq)) (Vector.to_list indf.params) in
    Inductiveops.make_ind_family ((Eq.cast InductiveDef.eq ind, univ), params)

  let get_arity (type env ind params nrealargs nrealdecls) (env : env Env.t)
      (indf : (env, ind, params, nrealargs, nrealdecls) t) :
      (env, nrealdecls) ERelContext.t =
    let Exists context =
      ERelContext.of_concrete (List.map EConstr.of_rel_decl (fst
        (Inductiveops.get_arity (Eq.cast Env.eq env) (to_concrete indf)))) in
    match Nat.is_eq (ERelContext.length context) indf.nrealdecls with
    | None -> assert false
    | Some Refl -> context

  let build_dependent_inductive  (type env ind params nrealargs nrealdecls)
      (env : env Env.t) (indf : (env, ind, params, nrealargs, nrealdecls) t) :
      (env * nrealdecls) ETerm.t =
    Eq.cast (Eq.sym ETerm.eq)
      (EConstr.of_constr (Inductiveops.build_dependent_inductive
         (Eq.cast Env.eq env) (to_concrete indf)))

  let map (type ind params nrealargs nrealdecls a b) (f : a Term.t -> b Term.t)
      (indf : (a, ind, params, nrealargs, nrealdecls) t) :
      (b, ind, params, nrealargs, nrealdecls) t =
    { indf with params = Vector.map f indf.params }
end

module InductiveType = struct
  type ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t = {
      family : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveFamily.t;
      realargs : ('env ETerm.t, 'nrealargs) Vector.t;
    }

  type 'env exists =
      Exists : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t -> 'env exists

  type ('env, 'ind) exists_ind =
      Exists :
        ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t ->
          ('env, 'ind) exists_ind

  let of_concrete (type env ind) (env : env Env.t)
      (ind_type : Inductiveops.inductive_type) :
      (env, ind) exists_ind =
    let family, realargs = Inductiveops.dest_ind_type ind_type in
    let Exists realargs =
      Vector.of_list (Eq.cast (Eq.list (Eq.sym ETerm.eq)) realargs) in
    let Exists family = InductiveFamily.of_concrete env family in
    match Nat.is_eq (Vector.length realargs) family.nrealargs with
    | None -> assert false
    | Some Refl -> Exists { family; realargs }

  let to_inductive_type (type env ind params nrealargs nrealdecls)
      (indt : (env, ind, params, nrealargs, nrealdecls) t) :
      Inductiveops.inductive_type =
    let family = InductiveFamily.to_concrete indt.family in
    Eq.(cast (sym ((Refl ^* Eq.list ETerm.eq) ^-> Refl)))
      Inductiveops.make_ind_type (family, Vector.to_list indt.realargs)

  let of_term_opt (type env ind) (env : env Env.t) (sigma : Evd.evar_map)
      (term : env ETerm.t) : (env, ind) exists_ind option =
    match
       Inductiveops.find_rectype (Eq.cast Env.eq env) sigma
        (Eq.cast ETerm.eq term)
    with
    | exception Not_found -> None
    | ind -> Some (of_concrete env ind)

  let of_term_opt_whd_all env sigma term =
    of_term_opt env sigma (ETerm.whd_all env sigma term)

  let map (type ind params realargs realdecls a b) (f : a Term.t -> b Term.t)
      (ef : a ETerm.t -> b ETerm.t)
      (ind_type : (a, ind, params, realargs, realdecls) t) :
      (b, ind, params, realargs, realdecls) t =
    { family = InductiveFamily.map f ind_type.family;
      realargs = Vector.map ef ind_type.realargs }

  let make_with_evars (type env ind) (env : env Env.t)
      (ind : ind InductiveDef.t) : (env, ind) exists_ind EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let nb_args =
      Inductiveops.inductive_nallargs (Eq.cast Env.eq env)
        (Eq.cast InductiveDef.eq ind) in
    let* args = EvarMapMonad.array_init nb_args (fun _ ->
      let* (e, _) = EvarMapMonad.new_type_evar env Evd.univ_flexible_alg in
      EvarMapMonad.new_evar env e) in
    let* sigma = EvarMapMonad.get in
    match of_term_opt env sigma (ETerm.mkApp (ETerm.mkInd ind) args) with
    | None -> assert false
    | Some (Exists ind) ->
        return (Exists ind)

  let make_case_or_project (type env ind params realargs realdecls)
    (env : env Env.t)
    (sigma : Evd.evar_map) (indt : (env, ind, params, realargs, realdecls) t)
    (style : Constr.case_style) ~(return_pred : env ETerm.t)
    ~(tomatch : env ETerm.t) (branches : (env ETerm.t, ind) Tuple.t) :
      env ETerm.t =
    let mind = indt.family.def in
    let rci =
      Eq.cast (Eq.sym Eq.(Env.eq ^-> Refl ^-> (InductiveDef.eq ^* Refl) ^->
        ETerm.eq ^-> ETerm.eq ^-> Refl))
      Typing.check_allowed_sort env sigma mind tomatch return_pred in
    let ci =
      Eq.cast (Eq.sym Eq.(Env.eq ^-> InductiveDef.eq ^-> Refl))
      Inductiveops.make_case_info env (fst mind) rci style in
    let indt = to_inductive_type indt in
    Eq.cast (Eq.sym Eq.(
      Env.eq ^-> Refl ^-> Refl ^-> Refl ^-> ETerm.eq ^-> ETerm.eq ^->
        Eq.trans Tuple.eq (Eq.array ETerm.eq) ^->
        ETerm.eq))
    Inductiveops.make_case_or_project env sigma indt ci return_pred
      tomatch branches
end

module TomatchType = struct
  type none = None

  type 'ind some = Some

  type ('env, 'ind, 'height) desc =
    | None : ('env, none, Nat.zero) desc
    | Some :
        ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveType.t ->
          ('env, 'ind some, 'nrealdecls Nat.succ) desc

  type ('env, 'ind) t =
      Exists : ('env, 'ind, 'height) desc -> ('env, 'ind) t
end

module TomatchTypes = AnnotatedVector.Make (TomatchType)

module ConstructorSummary = struct
  type ('env, 'ind, 'arity) t = {
      desc : Inductiveops.constructor_summary;
      cstr : 'ind Constructor.t;
      args : ('env, 'arity) RelContext.t;
      arity : 'arity Nat.t;
    }

  type ('env, 'ind) exists =
      Exists : ('env, 'ind, 'arity) t -> ('env, 'ind) exists

  let unsafe_make (desc : Inductiveops.constructor_summary)
      (cstr : 'ind Constructor.t) : ('env, 'ind) exists =
    let Exists args = RelContext.of_concrete desc.cs_args in
    Exists { desc; cstr; args; arity = RelContext.length args }

  let get (env : 'env Env.t)
      (indf : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveFamily.t)
      (specif : ('env, 'ind) InductiveSpecif.t)
      (cstr : 'ind Constructor.t) : ('env, 'ind) exists =
    let indu, params =
      Inductiveops.dest_ind_family (InductiveFamily.to_concrete indf) in
    let mib, mip = Eq.cast InductiveSpecif.eq specif in
    let desc =
      Inductiveops.get_constructor (indu, mib, mip, params)
        (Eq.cast Index.eq (Constructor.index cstr)) in
    unsafe_make desc cstr

  let get_tuple (env : 'env Env.t)
      (indf : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveFamily.t)
      (specif : ('env, 'ind) InductiveSpecif.t) :
      (('env, 'ind) exists, 'ind) Tuple.t =
    let ind, _ = indf.def in
    let nb = Tuple.length (InductiveSpecif.constructors specif) in
    Tuple.init nb (fun i -> get env indf specif (Constructor.make ind i))

  include Lift (struct
    module Phantom = struct
      type nonrec ('env, 'ind, 'arity) t = ('env, 'ind, 'arity) t
    end
    module Concrete = struct
      type t = Inductiveops.constructor_summary
    end
    let unsafe_map (type a b ind arity) f (summary : (a, ind, arity) t) :
        (b, ind, arity) t =
      let Exists result = unsafe_make (f summary.desc) summary.cstr in
      match
        Nat.is_eq (RelContext.length result.args)
          (RelContext.length summary.args) with
      | None -> assert false
      | Some Refl -> result
    let liftn n m (cs : Inductiveops.constructor_summary) :
        Inductiveops.constructor_summary = {
      cs_cstr = cs.cs_cstr;
      cs_params = List.map (Vars.liftn n m) cs.cs_params;
      cs_nargs = cs.cs_nargs;
      cs_args = RelContext.untyped_liftn n m cs.cs_args;
      cs_concl_realargs =
        Array.map (Vars.liftn n (m + cs.cs_nargs)) cs.cs_concl_realargs
    }
  end)
end

module type MeasurableS = sig
  type ('env, 'annot, 'height) t

  val height : ('env, 'annot, 'height) t -> 'height Height.t
end

module MeasurableVector (S : MeasurableS) = struct
  type ('env, 'length, 'annot, 'height, 'end_annot, 'end_height) section =
    | [] :
        ('env, Nat.zero, 'end_annot, 'end_height, 'end_annot,
         'end_height) section
    | (::) :
        ('env, 'annot_head, 'height_head) S.t *
        ('env, 'length, 'annot_tail, 'height_tail, 'end_annot, 'end_height)
        section ->
          ('env, 'length Nat.succ, 'annot_head * 'annot_tail,
            'height_head * 'height_tail, 'end_annot, 'end_height) section

  type ('env, 'length, 'annot, 'height) t =
      ('env, 'length, 'annot, 'height, unit, Nat.zero) section

  let rec height : type env length annot height .
        (env, length, annot, height) t -> height Height.t = fun v ->
    match v with
    | [] -> Height.zero
    | hd :: tl -> Height.add (S.height hd) (height tl)

  let rec partial_height : type env length annot height end_annot end_height .
        (env, length, annot, height, end_annot, end_height) section->
          (height, end_height) Height.diff = fun v ->
    match v with
    | [] -> Height.diff_zero
    | hd :: tl -> Height.diff_add (S.height hd) (partial_height tl)

  let rec length : type env length annot height end_annot end_height .
        (env, length, annot, height, end_annot, end_height) section ->
          length Nat.t = fun v ->
    match v with
    | [] -> Nat.O
    | _ :: tl -> Nat.S (length tl)

  let rec new_height : type env length annot height end_annot end_height.
        (env, length, annot, height) t -> height Height.t = fun v ->
    match v with
    | [] -> Height.zero
    | hd :: tl -> Height.add (S.height hd) (height tl)

  module type ProjS = sig
    module Type : BinaryTypeS

    val proj : ('env, 'annot, 'height) S.t -> ('env, 'annot) Type.t
  end

  module Proj (Item : ProjS) = struct
    module Vector = AnnotatedVector.Make (Item.Type)

    let rec proj : type env length annot height end_annot end_height .
          (env, length, annot, height, end_annot, end_height) section ->
            (env, length, annot, end_annot) Vector.section = fun v ->
      match v with
      | [] -> []
      | hd :: tl -> Item.proj hd :: proj tl
  end

  let rec append : type env length0 length1 length2 annot0 height0 annot1
        height1 annot2 height2.
    (env, length0, annot0, height0, annot1, height1) section ->
    (env, length1, annot1, height1, annot2, height2) section ->
    (length0, length1, length2) Nat.plus ->
    (env, length2, annot0, height0, annot2, height2) section =
  fun s0 s1 plus ->
    match s0, plus with
    | [], Nat.Zero_l -> s1
    | hd :: tl, Nat.Succ_plus plus -> hd :: (append tl s1 plus)

  type ('env, 'a) concat_map_f = {
    f : 'annot 'height . ('env, 'annot, 'height) S.t -> ('a, 'height) Vector.t
  }

  type ('env, 'height, 'a) concat_map =
    | Exists : {
        vector : ('a, 'height_sum) Vector.t;
        eq : ('height Env.t, 'height_sum Env.t) Eq.t;
      } -> ('env, 'height, 'a) concat_map

  let rec concat_map : type length annot height .
    ('env, 'a) concat_map_f -> ('env, length, annot, height) t ->
      ('env, height, 'a) concat_map =
  fun f v ->
    match v with
    | [] -> Exists { vector = []; eq = Refl }
    | hd :: tl ->
       let hd = f.f hd in
       let Exists { vector = tl; eq } = concat_map f tl in
       let Exists (new_length, plus) =
         Nat.add (Vector.length hd) (Vector.length tl) in
       let vector = Vector.append hd tl plus in
       Exists { vector;
         eq = Eq.trans (Env.morphism Refl eq) (Env.plus plus) }
end

module MeasurableVectorMap (S0 : MeasurableS) (S1 : MeasurableS) = struct
  module V0 = MeasurableVector (S0)

  module V1 = MeasurableVector (S1)

  type ('a, 'b) map =
      { f : 'annot 'height .
          ('a, 'annot, 'height) S0.t -> ('b, 'annot, 'height) S1.t }

  let rec map : type a b length annot height end_annot end_height .
        (a, b) map ->
          (a, length, annot, height, end_annot, end_height) V0.section ->
          (b, length, annot, height, end_annot, end_height) V1.section =
  fun f v ->
    match v with
    | [] -> []
    | hd :: tl -> f.f hd :: map f tl
end

exception NotAdjustable

let rec adjust_local_defs ?loc pats (args : _ Context.Rel.pt) :
    Glob_term.cases_pattern list =
  match pats, args with
  | (pat :: pats, LocalAssum _ :: decls) ->
      pat :: adjust_local_defs ?loc pats decls
  | (pats, LocalDef _ :: decls) ->
      (DAst.make ?loc @@ Glob_term.PatVar Anonymous) ::
      adjust_local_defs ?loc pats decls
  | [], [] -> []
  | _ -> raise NotAdjustable

module CasesPattern = struct
  type ('env, 'ind) desc =
    | Var
    | Cstr : {
      cstr : ('env, 'ind, 'arity) ConstructorSummary.t;
      args : (Glob_term.cases_pattern, 'arity) Vector.t;
    } -> ('env, 'ind TomatchType.some) desc

  type ('env, 'ind) content = {
      name : Names.Name.t;
      desc : ('env, 'ind) desc;
    }

  type ('env, 'ind) t = (('env, 'ind) content, [`any]) DAst.t

  let get_var (type ind) (pat : ('env, ind) t) : Names.Name.t option =
    let pat = DAst.get pat in
    match pat.desc with
    | Var -> Some pat.name
    | _ -> None

  let get_name (pat : ('env, 'ind) t) : Names.Name.t =
    (DAst.get pat).name

  let of_var (name : (Names.Name.t, [`any]) DAst.t) : ('env, 'ind) t =
    DAst.map (fun name -> { name; desc = Var }) name

  let unsafe_of_cstr
      (env : 'env Env.t)
      (cstrs : (('env, 'ind) ConstructorSummary.exists, 'ind) Tuple.t)
      (pat : (_, [`any]) DAst.t) : ('env, 'ind TomatchType.some) t =
    let loc = pat.CAst.loc in
    pat |> DAst.map (fun (cstr, args, alias) ->
      let cstr = Eq.cast (Eq.sym Constructor.eq) cstr in
      let index = Constructor.index cstr in
      let Exists summary = Tuple.Ops.(cstrs.%(index)) in
      let arity = RelContext.length summary.args in
      let args =
        match Vector.of_list_of_length args arity with
        | Some args -> args
        | None ->
            let args =
              try
                adjust_local_defs ?loc args (List.rev summary.desc.cs_args)
              with NotAdjustable ->
                Constructor.error_wrong_numarg ?loc env cstr
                  (Nat.to_int arity) in
            Option.get (Vector.of_list_of_length args arity) in
      { name = alias;
        desc = Cstr { cstr = summary; args }})

  let to_pat (pat : _ t) : Glob_term.cases_pattern =
    pat |> DAst.map (fun pat ->
      match pat.desc with
      | Var -> Glob_term.PatVar pat.name
      | Cstr { cstr; args } ->
          let cstr, _ = cstr.desc.cs_cstr in
          PatCstr (cstr, Vector.to_list args, pat.name))

  type 'item inferred =
    | Unknown : TomatchType.none inferred
    | Known : 'ind InductiveDef.t -> 'ind TomatchType.some inferred

  let get_cstr (pat : Glob_term.cases_pattern) =
    pat |> DAst.map (function
      | Glob_term.PatVar _ -> assert false
      | PatCstr (cstr, args, alias) -> (cstr, args, alias))

  let coerce_to ?loc (env : 'env Env.t) cstrs (pat : Glob_term.cases_pattern)
      (pat_ind : Names.inductive)
      (tgt_ind : 'ind InductiveDef.t) :
      ('env, 'ind TomatchType.some) t =
    unsafe_of_cstr env cstrs (get_cstr
      (Eq.cast (Eq.sym (Eq.arrow (Env.eq) (Eq.arrow Refl
        (Eq.arrow Refl (Eq.arrow InductiveDef.eq Refl)))))
          (Coercion.inh_pattern_coerce_to ?loc) env pat pat_ind
            tgt_ind))

  type ('a, 'b) map = {
      f : 'ind 'arity .
        ('a, 'ind, 'arity) ConstructorSummary.t ->
          ('b, 'ind, 'arity) ConstructorSummary.t
    }

  let map (type a b ind) f (t : (a, ind) t) : (b, ind) t =
    t |> DAst.map (fun ({ name; desc } : (a, ind) content) ->
      let desc : (b, ind) desc =
        match desc with
        | Var -> Var
        | Cstr { cstr; args } -> Cstr { cstr = f.f cstr; args } in
      { name; desc })

  let lift n p = map { f = fun cstr -> ConstructorSummary.lift n cstr } p

  let check
      (type env ind params nrealargs nrealdecls)
      (env : env Env.t)
      (cstrs : ((env, ind) ConstructorSummary.exists, ind) Tuple.t)
      (ind_type : (env, ind, params, nrealargs, nrealdecls) InductiveType.t)
      (pat : Glob_term.cases_pattern) =
    match DAst.get pat with
    | PatVar name ->
        of_var (pat |> DAst.map (fun _ -> name))
    | PatCstr (cstr, args, alias) ->
        let ind, _ = ind_type.family.def in
        let Exists cstr' = Constructor.of_constructor cstr in
        let ind' = Names.inductive_of_constructor cstr in
        if Names.eq_ind (Eq.cast InductiveDef.eq ind) ind' then
          unsafe_of_cstr env cstrs
            (pat |> DAst.map (fun _ -> (cstr, args, alias)))
        else
          let loc = pat.CAst.loc in
          try
            coerce_to ?loc env cstrs pat ind' ind
          with Not_found ->
            Constructor.error_bad ?loc:pat.CAst.loc env cstr' ind
end

module CasesPatterns = struct
  include AnnotatedVector.Make (CasesPattern)

  let lift n v = map { f = fun p -> CasesPattern.lift n p } v
end

module Tomatch = struct
  type ('env, 'ind, 'height) t = {
      judgment : 'env EJudgment.t;
      inductive_type : ('env, 'ind, 'height) TomatchType.desc;
      return_pred_height : 'height Height.t;
    }

  let height t = t.return_pred_height

  let map (type a b ind length)
      (f : a Term.t -> b Term.t) (ef : a ETerm.t -> b ETerm.t)
      (tomatch : (a, ind, length) t) : (b, ind, length) t =
    { judgment = EJudgment.map ef tomatch.judgment;
      inductive_type =
        begin match tomatch.inductive_type with
        | None -> None
        | Some ind -> Some (InductiveType.map f ef ind)
        end;
      return_pred_height = tomatch.return_pred_height; }
end

module TomatchVector = struct
  include MeasurableVector (Tomatch)

  include MeasurableVectorMap (Tomatch) (Tomatch)

  let lift n tomatches =
    map { f = fun t -> Tomatch.map (Term.lift n) (ETerm.lift n) t } tomatches
end

module Rhs = struct
  type 'env t =
    | Glob_constr of Glob_term.glob_constr
    | EJudgment of 'env EJudgment.t

  let map f rhs =
    match rhs with
    | Glob_constr c -> Glob_constr c
    | EJudgment j -> EJudgment (EJudgment.map f j)
end

module Clause = struct
  type ('env, 'pats) desc = {
      env : 'env GlobalEnv.t;
      ids : Names.Id.Set.t;
      pats : 'pats;
      rhs : 'env Rhs.t;
    }

  type ('env, 'pats) t = ('env, 'pats) desc CAst.t

  let extract_pat_var (type env length head tail)
      (clause : (env, (env, length, head * tail) CasesPatterns.t) t) :
      Names.Name.t option =
    match clause.v.pats with
    | head :: _ -> CasesPattern.get_var head
end

module PrepareTomatch (EqnLength : Type) = struct
  module TomatchWithContext = struct
    type ('env, 'ind, 'height) t = {
        tomatch : ('env, 'ind, 'height) Tomatch.t;
        return_pred_context : ('env, 'height) ERelContext.with_height;
        pats : (('env, 'ind) CasesPattern.t, EqnLength.t) Vector.t;
      }

    type 'env exists =
        Exists : ('env, 'ind, 'height) t -> 'env exists

    let height t = Tomatch.height t.tomatch

    type ('env, 'item) inferred =
      | Unknown : ('env, TomatchType.none) inferred
      | Known :
          ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveType.t ->
            ('env, 'ind TomatchType.some) inferred

    type 'env infer_type =
        Inferred :
          ('env, 'ind) inferred *
          (('env, 'ind) CasesPattern.t, EqnLength.t) Vector.t ->
            'env infer_type

    let rec check :
      type env ind params nrealargs nrealdecls pat_length accu_length .
          env Env.t ->
          (pat_length, accu_length, EqnLength.t) Nat.plus ->
          (env, ind, params, nrealargs, nrealdecls) InductiveType.t ->
          ((env, ind) ConstructorSummary.exists, ind) Tuple.t ->
          (Glob_term.cases_pattern, pat_length) Vector.t ->
          ((env, ind TomatchType.some) CasesPattern.t, accu_length)
              Vector.t ->
          env infer_type = fun env plus ind_type cstrs pats accu ->
      match pats, plus with
      | [], Zero_l ->
          Inferred (
            Known ind_type, Vector.map_rev_append Fun.id accu []
              (Nat.plus_commut (Vector.length accu) plus))
      | hd :: tl, Succ_plus plus ->
          let pat = CasesPattern.check env cstrs ind_type hd in
          check env (Nat.plus_succ plus) ind_type cstrs tl (pat :: accu)

    let rec infer : type pat_length var_length .
          'env Env.t ->
          (pat_length, var_length, EqnLength.t) Nat.plus ->
          (Glob_term.cases_pattern, pat_length) Vector.t ->
          ((Names.Name.t, [`any]) DAst.t, var_length) Vector.t ->
          'env infer_type EvarMapMonad.t =
    fun env plus pats vars ->
      let open EvarMapMonad.Ops in
      match pats, plus with
      | [], Zero_l ->
          return (Inferred (
            Unknown,
            Vector.map_rev_append CasesPattern.of_var vars []
              (Nat.plus_commut (Vector.length vars) plus)))
      | hd :: tl, Succ_plus plus  ->
          match DAst.get hd with
          | PatVar name ->
              infer env (Nat.plus_succ plus) tl
                (DAst.map (fun _ -> name) hd :: vars)
          | PatCstr (cstr, args, alias) ->
              let Exists cstr' = Constructor.of_constructor cstr in
              let ind = Constructor.inductive cstr' in
              let vars_pat =
                Vector.map_rev_append CasesPattern.of_var vars []
                  (Nat.zero_r (Vector.length vars)) in
              let* Exists ind_type = InductiveType.make_with_evars env ind in
              let pat = hd |> DAst.map (fun _ -> (cstr, args, alias)) in
              let specif = InductiveSpecif.lookup env ind in
              let cstrs =
                ConstructorSummary.get_tuple env ind_type.family specif in
              return (check env (Nat.plus_succ plus) ind_type cstrs tl
                (CasesPattern.unsafe_of_cstr env cstrs pat :: vars_pat))

    let infer_type  (type env) (env : env Env.t)
        (sigma : Evd.evar_map) (judgment : env EJudgment.t)
        (pats : (Glob_term.cases_pattern, EqnLength.t) Vector.t) :
        env infer_type EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      match
        InductiveType.of_term_opt_whd_all env sigma
          (EJudgment.uj_type judgment)
      with
      | None ->
          infer env (Nat.zero_r (Vector.length pats)) pats []
      | Some (Exists ind_type) ->
          let ind, _ = ind_type.family.def in
          let specif = InductiveSpecif.lookup env ind in
          let cstrs =
            ConstructorSummary.get_tuple env ind_type.family specif in
          return (check env (Nat.zero_r (Vector.length pats)) ind_type cstrs
            pats [])

    let make (type env) (env : env Env.t)
        (judgment : env EJudgment.t)
        (predicate_pattern : Glob_term.predicate_pattern)
        (pats : (Glob_term.cases_pattern, EqnLength.t) Vector.t) :
        env exists EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let* sigma = EvarMapMonad.get in
      let* Inferred (inferred, pats) = infer_type env sigma judgment pats in
      match inferred with
      | Unknown ->
          return (Exists {
            tomatch = {
              judgment;
              inductive_type = None;
              return_pred_height = Height.zero;
            };
            return_pred_context = Exists ([], Refl);
            pats;
          })
      | Known inductive_type ->
          let arity = InductiveFamily.get_arity env inductive_type.family in
          let as_name, in_names = predicate_pattern in
          let ty =
            InductiveFamily.build_dependent_inductive env
              inductive_type.family in
          let return_pred_context : (_, _) ERelContext.t =
            EDeclaration.assum
              (Context.make_annot as_name Relevant) ty :: arity in
          let return_pred_height =
            Height.of_nat (ERelContext.length return_pred_context) in
          return (Exists {
            tomatch = {
              judgment;
              inductive_type = Some inductive_type;
              return_pred_height;
            };
            return_pred_context = Exists (return_pred_context, Refl);
            pats;
          })
  end

  module TomatchWithContextVector = struct
    include MeasurableVector (TomatchWithContext)

    let to_tomatch_vector v =
      let module Map =
        MeasurableVectorMap (TomatchWithContext)
          (Tomatch) in
      Map.map { f = fun tomatch -> tomatch.tomatch } v

    let to_clauses (type env) (env : env GlobalEnv.t)
        (clauses : (Glob_term.cases_clause, EqnLength.t) Vector.t)
        (v : (env, 'length, 'ind, 'height) t) :
        ((env, (env, 'length, 'ind) CasesPatterns.t) Clause.t, EqnLength.t)
          Vector.t =
      clauses |> Vector.mapi (fun index clause ->
        clause |> CAst.map (fun (ids, pats, rhs) : (env, _) Clause.desc ->
          let module P = Proj (struct
            module Type = CasesPattern

            let proj (v : ('env, 'annot, 'height) TomatchWithContext.t) =
              Vector.Ops.(v.pats.%(index))
          end) in
          let pats = P.proj v in
          { env; ids = Names.Id.Set.of_list ids; pats; rhs = Glob_constr rhs }))

    type ('env, 'return_pred_height) make_return_pred_context =
        Exists :
          ('env, 'height) ERelContext.t * 'height Nat.t *
          ('height Env.t, 'return_pred_height Env.t) Eq.t ->
            ('env, 'return_pred_height) make_return_pred_context

    let rec make_return_pred_context :
    type env length annot return_pred_height .
          env Env.t -> Evd.evar_map ->
            (env, length, annot, return_pred_height) t ->
            (env, return_pred_height) make_return_pred_context =
    fun env sigma tomatchl ->
      match tomatchl with
      | [] -> Exists ([], Nat.O, Refl)
      | { return_pred_context = Exists (return_pred_context, eq_return);
          tomatch = { return_pred_height; _ }} :: tl ->
          let height = ERelContext.length return_pred_context in
          let Exists (tl, length, eq_tl) =
            make_return_pred_context env sigma tl in
          let Exists (sum, plus) = Nat.add height length in
          let context =
            ERelContext.push
              (ERelContext.lift (Height.of_nat length) return_pred_context) tl
              plus in
          Exists (context, sum, Eq.trans (Eq.sym (Env.plus plus))
            (Env.morphism eq_return eq_tl))
      | _ -> .

    type ('env, 'length, 'end_annot, 'end_height) exists =
        Exists :
          ('env, 'length, 'ind, 'return_pred_height, 'end_annot, 'end_height)
          section -> ('env, 'length, 'end_annot, 'end_height) exists

    let rec of_vector : type env tomatch_length end_annot end_height .
          (env TomatchWithContext.exists, tomatch_length) Vector.t ->
            (env, tomatch_length, end_annot, end_height) exists = fun l ->
      match l with
      | [] -> Exists []
      | Exists hd :: tl ->
          let Exists tl = of_vector tl in
          Exists (hd :: tl)
  end
end

module ReturnPred = struct
  type ('env, 'return_pred_height) t =
    | ReturnPred of {
        return_pred : ('env * 'return_pred_height) ETerm.t;
        return_pred_height : 'return_pred_height Height.t;
      }
    | Tycon of 'env ETerm.t option

  type ('a, 'b) map = {
      f : 'n . ('a * 'n) ETerm.t -> ('b * 'n) ETerm.t
    }

  let map (type a b height) (f : (a, b) map) (p : (a, height) t) :
      (b, height) t =
    match p with
    | ReturnPred { return_pred; return_pred_height } ->
        ReturnPred { return_pred = f.f return_pred; return_pred_height }
    | Tycon tycon ->
        Tycon (Option.map
          (Eq.cast (Eq.arrow (ETerm.morphism Env.zero_r)
            (ETerm.morphism Env.zero_r)) f.f) tycon)

  let morphism (type a b c d) (eq_env : (a Env.t, b Env.t) Eq.t)
      (eq_height : (c Env.t, d Env.t) Eq.t)
      (p : (a, c) t) : (b, d) t =
    match p with
    | ReturnPred { return_pred; return_pred_height } ->
        ReturnPred {
          return_pred = Eq.cast (ETerm.morphism (Env.morphism eq_env eq_height))
            return_pred;
          return_pred_height =
            Eq.cast (Height.morphism eq_height) return_pred_height;
        }
    | Tycon tycon ->
        Tycon (Eq.cast (Eq.option (ETerm.morphism eq_env)) tycon)

  let return_pred_eq (type a b c) () :
      (((a * b) * c) Env.t, ((a * c) * b) Env.t) Eq.t =
    Eq.trans Env.assoc
      (Eq.trans (Env.pair Refl Env.commut) (Eq.sym Env.assoc))

  let lift n p =
    match p with
    | Tycon tycon -> Tycon (Option.map (ETerm.lift n) tycon)
    | ReturnPred { return_pred; return_pred_height } ->
        ReturnPred {
          return_pred = ETerm.liftn n return_pred_height return_pred;
          return_pred_height;
      }

  let lift_in_return_pred (type env n return_pred_height)
      (n : n Height.t) (p : (env, return_pred_height) t) :
      (env, n * return_pred_height) t =
    match p with
    | Tycon tycon -> Tycon tycon
    | ReturnPred { return_pred; return_pred_height } ->
        ReturnPred {
          return_pred = Eq.cast (ETerm.morphism Env.assoc)
            (ETerm.liftn n return_pred_height return_pred);
          return_pred_height = Height.add n return_pred_height;
      }
end

module PatternMatchingProblem = struct
  type ('env, 'tomatch_length, 'tomatch_ind, 'eqn_length,
      'return_pred_height) t = {
      env : 'env GlobalEnv.t;
      tomatches :
        ('env, 'tomatch_length, 'tomatch_ind, 'return_pred_height)
        TomatchVector.t;
      eqns :
        (('env, ('env, 'tomatch_length, 'tomatch_ind) CasesPatterns.t) Clause.t,
          'eqn_length) Vector.t;
      return_pred : ('env, 'return_pred_height) ReturnPred.t;
    }
end

module type MatchContextS = sig
  val typing_fun : compile_cases_typing_fun

  val style : Constr.case_style

  val program_mode : bool

  val compile_loop :
      ('env, 'tomatch_length, 'tomatch_ind, 'eqns_length, 'return_pred_height)
        PatternMatchingProblem.t -> 'env EJudgment.t EvarMapMonad.t
end

let naming_of_program_mode (program_mode : bool) : Evarutil.naming_mode =
  if program_mode then ProgramNaming
  else KeepUserNameAndRenameExistingButSectionNames

module type CompilerS = sig
  val compile_cases :
      ?tycon:'env ETerm.t -> Constr.case_style -> 'env GlobalEnv.t ->
      Glob_term.glob_constr option ->
      Glob_term.tomatch_tuple list ->
      (Glob_term.cases_clause, 'eqns_length) Vector.t ->
      'env EJudgment.t EvarMapMonad.t

  val compile_loop :
      ('env, 'tomatch_length, 'tomatch_ind, 'eqns_length, 'return_pred_height)
        PatternMatchingProblem.t -> 'env EJudgment.t EvarMapMonad.t
end

module Make (MatchContext : MatchContextS) : CompilerS = struct
  module Typer = struct
    let judgment_of_glob_constr (type env) ?(tycon : env ETerm.t option)
        (env : env GlobalEnv.t)
        (constr : Glob_term.glob_constr) :
        (env EJudgment.t) EvarMapMonad.t =
      Eq.cast (EvarMapMonad.eq (Eq.sym EJudgment.eq) Refl)
        (fun (sigma : Evd.evar_map) ->
          MatchContext.typing_fun (Eq.cast (Eq.option ETerm.eq) tycon)
            (Eq.cast GlobalEnv.eq env) sigma
            constr)
  end

  module TomatchTuple = struct
    type 'env t = {
        judgment : 'env EJudgment.t;
        predicate_pattern : Glob_term.predicate_pattern;
      }

    let of_judgment (judgment : 'env EJudgment.t) : 'env t =
      { judgment; predicate_pattern = (Anonymous, None) }

    let of_tomatch_tuple (env : 'env GlobalEnv.t)
        (tuple : Glob_term.tomatch_tuple) : 'env t EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let term, predicate_pattern = tuple in
      let* judgment = Typer.judgment_of_glob_constr env term in
      return { judgment; predicate_pattern }
  end

  module TypeTomatch (EqnLength : TypeS) = struct
    module PrepareTomatch = PrepareTomatch (EqnLength)

    let type_tomatch (glob_env : 'env GlobalEnv.t)
        (tomatch_with_pats :
           'env TomatchTuple.t *
           (Glob_term.cases_pattern, EqnLength.t) Vector.t):
        'env PrepareTomatch.TomatchWithContext.exists EvarMapMonad.t =
      let tuple, pats = tomatch_with_pats in
      let env = GlobalEnv.env glob_env in
      PrepareTomatch.TomatchWithContext.make env tuple.judgment
        tuple.predicate_pattern pats

    let type_tomatches
        (type tomatch_length end_annot end_height)
        (env : 'env GlobalEnv.t)
        (tomatches_with_pats :
           ('env TomatchTuple.t *
               (Glob_term.cases_pattern, EqnLength.t) Vector.t,
             tomatch_length) Vector.t) :
        ('env, tomatch_length, end_annot, end_height)
        PrepareTomatch.TomatchWithContextVector.exists EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let module VectorUtils = Vector.UseMonad (StateMonad) in
      let* vector =
        VectorUtils.map (type_tomatch env) tomatches_with_pats in
      return (PrepareTomatch.TomatchWithContextVector.of_vector vector)
  end

  let compile_base (type env)
      (problem :
         (env, Nat.zero, unit, _ Nat.succ, Nat.zero) PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let env, rhs =
      match problem.eqns with
      | { v = { env; rhs; _ }} :: _ -> env, rhs in
    match rhs with
    | Glob_constr glob_constr ->
        begin match problem.return_pred with
        | Tycon tycon ->
            Typer.judgment_of_glob_constr ?tycon env glob_constr
        | ReturnPred { return_pred } ->
            let* judgment =
              Typer.judgment_of_glob_constr ~tycon:return_pred
                (Eq.cast (GlobalEnv.morphism (Eq.sym Env.zero_r)) env)
                glob_constr in
            let* (judgment, _trace) =
              EJudgment.inh_conv_coerce_to
                ~program_mode:MatchContext.program_mode
                ~resolve_tc:true (GlobalEnv.env env)
                judgment return_pred in
            return (EJudgment.morphism Env.zero_r judgment)
        end
    | EJudgment judgment -> return judgment

  let is_compile_case_trivial
      (type env ind length_tail ind_tail eqns_length return_pred_height
        tail_height)
      (sigma : Evd.evar_map)
      (tomatch : (env, ind, return_pred_height) Tomatch.t)
      (tomatches : (env, length_tail, ind_tail, tail_height) TomatchVector.t)
      (problem :
         (env, length_tail Nat.succ, ind * ind_tail, eqns_length,
           return_pred_height * tail_height) PatternMatchingProblem.t) :
      ((Names.Name.t, eqns_length) Vector.t *
        (env, tail_height) ReturnPred.t) option =
    let open OptionMonad.Ops in
    let module VectorUtils = Vector.UseMonad (OptionMonad) in
    let* vars = VectorUtils.map Clause.extract_pat_var problem.eqns in
    let* () = match vars with [] -> None | _ :: _ -> Some () in
    let* return_pred =
      match problem.return_pred with
      | ReturnPred { return_pred; return_pred_height } ->
          if ETerm.noccur_between sigma 1
              (Height.to_int return_pred_height) return_pred then
            match Height.to_nat tomatch.return_pred_height with
            | Exists (nat, eq) ->
                let substl = Vector.make nat (ETerm.mkProp ()) in
                let tail_height = TomatchVector.height tomatches in
                let return_pred =
                  Eq.cast (ETerm.morphism (Eq.trans (Eq.sym Env.assoc)
                    (Env.pair (Env.pair Refl (Eq.sym eq)) Refl)))
                    return_pred in
                return (ReturnPred.ReturnPred
                  { return_pred =
                      ETerm.substnl substl tail_height return_pred;
                    return_pred_height = tail_height })
          else
            None
      | Tycon o -> return (ReturnPred.Tycon o) in
    return (vars, return_pred)

  let compile_case_trivial
      (type env ind tail_length ind_tail eqns_length return_pred_height
        tail_height)
      (tomatch : (env, ind, return_pred_height) Tomatch.t)
      (vars : (Names.Name.t, eqns_length) Vector.t)
      (return_pred : (env, tail_height) ReturnPred.t)
      (tomatches : (env, tail_length, ind_tail, tail_height) TomatchVector.t)
      (problem :
         (env, tail_length Nat.succ, ind * ind_tail, eqns_length,
           return_pred_height * tail_height) PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* sigma = EvarMapMonad.get in
    let self_name =
      try
        Vector.find (fun (name : Names.Name.t) -> name <> Anonymous) vars
      with Not_found -> Anonymous in
    let push name env =
      GlobalEnv.push_rel
        ~hypnaming:KeepUserNameAndRenameExistingButSectionNames sigma
        (EDeclaration.local_def (Context.annotR name) tomatch.judgment)
        env in
    let _declaration, env = push self_name problem.env in
    let tomatches = TomatchVector.lift Height.one tomatches in
    let eqns =
      Vector.map2
        (fun (var : Names.Name.t) ->
          CAst.map (fun
            (desc : (env, (env, tail_length Nat.succ, ind * ind_tail)
              CasesPatterns.t) Clause.desc) :
            (env * Nat.zero Nat.succ,
              (env * Nat.zero Nat.succ, tail_length, ind_tail)
                CasesPatterns.t) Clause.desc ->
            let _, env = push var desc.env in
            let _ :: pats = desc.pats in
            let pats = CasesPatterns.lift Height.one pats in
            let rhs = Rhs.map (ETerm.lift Height.one) desc.rhs in
            { env; ids = desc.ids; pats; rhs })) vars problem.eqns in
    let return_pred = ReturnPred.lift Height.one return_pred in
    let* judgment =
      MatchContext.compile_loop { env; tomatches; eqns; return_pred } in
    return (EJudgment.map (ETerm.subst1 (EJudgment.uj_val tomatch.judgment))
      judgment)

  type ('env, 'arity, 'tail_length, 'ind_tail) prepare_clause =
      ('env, (Glob_term.cases_pattern, 'arity) Vector.t *
          ('env, 'tail_length, 'ind_tail) CasesPatterns.t) Clause.t

  type ('env, 'arity, 'eqn_length, 'end_annot, 'end_height)
        prepare_sub_tomatches =
      Exists : {
      env : ('env * 'arity) GlobalEnv.t;
      section :
        ('env * 'arity, 'arity, 'annot, 'height, 'end_annot, 'end_height)
        TomatchVector.section;
      pats : (('env * 'arity, 'arity, 'annot, 'end_annot) CasesPatterns.section,
        'eqn_length) Vector.t;
    } -> ('env, 'arity, 'eqn_length, 'end_annot, 'end_height)
        prepare_sub_tomatches

  let prepare_sub_tomatches
      (type env ind tail_length ind_tail eqn_length arity end_annot end_height)
      (env : env GlobalEnv.t)
      (args : (env, arity) ERelContext.t)
      (clauses : ((env, arity, tail_length, ind_tail) prepare_clause,
        eqn_length) Vector.t) :
      (env, arity, eqn_length, end_annot, end_height) prepare_sub_tomatches
        EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let open Vector.Ops in
    let module EqnLength = struct type t = eqn_length end in
    let module T = TypeTomatch (EqnLength) in
    let tomatches =  ERelContext.to_rel_vector args in
    let tomatches =
      tomatches |> Vector.mapi (
      fun (i : arity Diff.t) (judgment : (env * arity) EJudgment.t) ->
        TomatchTuple.of_judgment judgment,
        clauses |> Vector.map (
        fun (clause : (env, arity, tail_length, ind_tail) prepare_clause) ->
          let patterns, tail = clause.v.pats in
          patterns.%(i))) in
    let* sigma = EvarMapMonad.get in
    let hypnaming = naming_of_program_mode MatchContext.program_mode in
    let _, env =
      GlobalEnv.push_rel_context ~hypnaming sigma args env in
    let* Exists tomatches = T.type_tomatches env tomatches in
    let module V = T.PrepareTomatch.TomatchWithContextVector in
    let section = V.to_tomatch_vector tomatches in
    let pats =
      clauses |> Vector.mapi (fun index _ ->
        let module P = V.Proj (struct
          module Type = CasesPattern
          let proj (v :
              ('env, 'annot, 'height) T.PrepareTomatch.TomatchWithContext.t) =
            Vector.Ops.(v.pats.%(index))
        end) in
        P.proj tomatches) in
    return (Exists { env; section; pats })

  type ('env, 'ind, 'tail_length, 'ind_tail) branch_clauses =
      Exists : {
      summary : ('env, 'ind, 'arity) ConstructorSummary.t;
      clauses : ('env, 'arity, 'tail_length, 'ind_tail) prepare_clause list;
    } -> ('env, 'ind, 'tail_length, 'ind_tail) branch_clauses

  let compile_branch
      (type env ind tail_length ind_tail eqns_length return_pred_height
         tail_height)
      (tomatch : (env, ind TomatchType.some, return_pred_height) Tomatch.t)
      (tomatches : (env, tail_length, ind_tail, tail_height) TomatchVector.t)
      (problem :
         (env, tail_length Nat.succ, ind TomatchType.some * ind_tail,
           eqns_length, return_pred_height * tail_height)
         PatternMatchingProblem.t)
      (return_pred : (env, tail_height) ReturnPred.t)
      (Exists { summary; clauses } :
         (env, ind, tail_length, ind_tail) branch_clauses) :
      env ETerm.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* sigma = EvarMapMonad.get in
    let args = ERelContext.of_rel_context summary.args in
    let height = Height.of_nat summary.arity in
    let tomatches = TomatchVector.lift height tomatches in
    let Exists clauses = Vector.of_list (List.rev clauses) in
    let* Exists prepare = prepare_sub_tomatches problem.env args clauses in
    let* sigma = EvarMapMonad.get in
    let Exists (_, plus) =
      Nat.add (TomatchVector.length prepare.section)
        (TomatchVector.length tomatches) in
    let eqns =
      clauses |> Vector.mapi (fun i ->
        CAst.map (fun (desc : (_, _) Clause.desc) : (_, _) Clause.desc ->
          let new_pats = Vector.Ops.(prepare.pats.%(i)) in
          let names =
            new_pats |> CasesPatterns.to_vector { f = CasesPattern.get_name } in
          let context = ERelContext.set_names names args in
          let hypnaming = naming_of_program_mode MatchContext.program_mode in
          let _, env =
            GlobalEnv.push_rel_context ~hypnaming sigma context desc.env in
          let old_pats = CasesPatterns.lift height (snd desc.pats) in
          let pats = CasesPatterns.append new_pats old_pats plus in
          let rhs = Rhs.map (ETerm.lift height) desc.rhs in
          { env; ids = desc.ids; pats; rhs })) in
    let new_tomatches =
      TomatchVector.append prepare.section tomatches plus in
    let Exists return_pred_height =
      TomatchVector.partial_height prepare.section in
    let return_pred =
      ReturnPred.morphism Refl return_pred_height.plus
        (ReturnPred.lift_in_return_pred return_pred_height.diff
          (ReturnPred.lift height return_pred)) in
    let sub_problem = {
      PatternMatchingProblem.env = prepare.env;
      tomatches = new_tomatches; eqns;
      return_pred; } in
    let* j = MatchContext.compile_loop sub_problem in
    return (ERelContext.it_mkLambda_or_LetIn (EJudgment.uj_val j) args)

  let get_tomatch_args : type env ind height .
      (env, ind, height) Tomatch.t -> (env ETerm.t, height) Vector.t =
  fun tomatch ->
    match tomatch.inductive_type with
    | None -> []
    | Some inductive_type ->
        let Refl = match
          Nat.is_eq
            inductive_type.family.nrealargs
            inductive_type.family.nrealdecls with
        | Some eq -> eq
        | None -> failwith "Not implemented!" in
        EJudgment.uj_val tomatch.judgment :: inductive_type.realargs

  let compile_destruct
      (type env ind params nrealargs nrealdecls tail_length ind_tail eqns_length
        return_pred_height tail_height)
      (tomatch : (env, ind TomatchType.some, return_pred_height) Tomatch.t)
      (ind : (env, ind, params, nrealargs, nrealdecls) InductiveType.t)
      (tomatches : (env, tail_length, ind_tail, tail_height) TomatchVector.t)
      (problem :
        (env, tail_length Nat.succ, ind TomatchType.some * ind_tail,
          eqns_length, return_pred_height * tail_height)
            PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    let open Tuple.Ops in
    let env = GlobalEnv.env problem.env in
    let specif = InductiveSpecif.lookup env (fst (ind.family.def)) in
    let constructors = InductiveSpecif.constructors specif in
    let constructor_summaries =
      ConstructorSummary.get_tuple env ind.family specif in
    let nb_cstr = Tuple.length constructors in
    let branches = Tuple.init nb_cstr (fun i ->
      let Exists summary = constructor_summaries.%(i) in
      Exists { summary; clauses = [] }) in
    let add_eqn (clause : (env, (env, tail_length Nat.succ, ind TomatchType.some * ind_tail) CasesPatterns.t) Clause.t) =
      let pat :: tail = clause.v.pats in
      match (DAst.get pat).desc with
      | Var ->
          Tuple.iter branches (fun i ->
            let Exists { summary; clauses } = branches.%(i) in
            let clause =
              clause |> CAst.map (fun (desc : (_, _) Clause.desc) ->
                { desc with pats = (Vector.make summary.arity
                (DAst.make (Glob_term.PatVar Anonymous)), tail) }) in
            branches.%(i) <- Exists {
              summary; clauses = clause :: clauses })
      | Cstr { cstr; args } ->
          let i = Constructor.index cstr.cstr in
          let Exists { summary; clauses } = branches.%(i) in
          let Refl = Option.get (Nat.is_eq summary.arity cstr.arity) in
          let clause =
            clause |> CAst.map (fun (desc : (_, _) Clause.desc) ->
              { desc with pats = (args, tail) }) in
          branches.%(i) <- Exists {
            summary; clauses = clause :: clauses } in
    Vector.iter add_eqn problem.eqns;
    let open EvarMapMonad.Ops in
    let* sigma = EvarMapMonad.get in
    let* return_pred =
      match problem.return_pred with
      | ReturnPred { return_pred; return_pred_height } ->
          let args = get_tomatch_args tomatch in
          let tail_height = TomatchVector.height tomatches in
          return (ReturnPred.ReturnPred {
            return_pred = ETerm.substnl args tail_height
              (Eq.(cast (sym (ETerm.morphism Env.assoc)) return_pred));
            return_pred_height = tail_height; })
      | Tycon tycon ->
          return (ReturnPred.Tycon tycon) in
    let* branches =
      branches |> EvarMapMonad.tuple_map
        (compile_branch tomatch tomatches problem return_pred) in
    let* return_pred =
      match return_pred with
      | ReturnPred { return_pred; return_pred_height } ->
          let Exists { vector; eq } =
            TomatchVector.concat_map { f = get_tomatch_args } tomatches in
          return (ETerm.substl vector
            (Eq.cast (ETerm.morphism (Env.morphism Refl eq)) return_pred))
      | Tycon None ->
          let* ty, _ =
            EvarMapMonad.new_type_evar (GlobalEnv.env problem.env)
              Evd.univ_flexible_alg in
          return ty
      | Tycon (Some tycon) ->
          return tycon in
    let case =
      InductiveType.make_case_or_project (GlobalEnv.env problem.env) sigma ind
        MatchContext.style ~tomatch:(EJudgment.uj_val tomatch.judgment)
        ~return_pred branches in
    return (EJudgment.make case return_pred)

  let compile_case
      (type env ind tail_length ind_tail eqns_length return_pred_height
        tail_height)
      (tomatch : (env, ind, return_pred_height) Tomatch.t)
      (tomatches : (env, tail_length, ind_tail, tail_height) TomatchVector.t)
      (problem :
         (env, tail_length Nat.succ, ind * ind_tail, eqns_length,
           return_pred_height * tail_height) PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* sigma = EvarMapMonad.get in
    match is_compile_case_trivial sigma tomatch tomatches problem with
    | Some (vars, return_pred) ->
        compile_case_trivial tomatch vars return_pred tomatches problem
    | None ->
        match tomatch.inductive_type with
        | None -> assert false
        | Some ind ->
            compile_destruct tomatch ind tomatches problem

  let compile_loop (type env tomatch_length ind eqns_length return_pred_height)
      (problem :
         (env, tomatch_length, ind, eqns_length, return_pred_height)
         PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    match problem.tomatches with
    | [] ->
        begin
          match problem.eqns with
          | [] -> assert false
          | _ :: _ -> compile_base problem
        end
    | tomatch :: tomatches ->
        compile_case tomatch tomatches problem

  let compile_cases (type env eqns_length)
      ?(tycon : env ETerm.t option)
      (style : Constr.case_style) (env : env GlobalEnv.t)
      (predopt : Glob_term.glob_constr option)
      (tomatches : Glob_term.tomatch_tuple list)
      (eqns : (Glob_term.cases_clause, eqns_length) Vector.t) :
      env EJudgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let module EqnLength = struct type t = eqns_length end in
    let module T = TypeTomatch (EqnLength) in
    let Exists tomatches = Vector.of_list tomatches in
    let pats = eqns |> Vector.map (fun (eqn : Glob_term.cases_clause) ->
      let _id, pats, _rhs = eqn.v in
      pats) in
    let module M = Vector.UseMonad (StateMonad) in
    let empty_pats, tomatches =
      let open StateMonad.Ops in
      StateMonad.run pats (
        M.map (fun tomatch ->
          let* pats = StateMonad.get in
          let pat, pats =
            Vector.map_split (fun pats ->
              match pats with
              | [] -> assert false
              | hd :: tl -> hd, tl) pats in
          let* () = StateMonad.set pats in
          return (tomatch, pat)) tomatches) in
    assert (Vector.for_all (fun pats -> pats = []) empty_pats);
    let* tomatches =
      M.map (fun (tuple, pats) ->
        let* tuple = TomatchTuple.of_tomatch_tuple env tuple in
        return (tuple, pats)) tomatches in
    let* Exists tomatches = T.type_tomatches env tomatches in
    let* sigma = EvarMapMonad.get in
    let Exists (return_pred_context, return_pred_height, eq_return_height) =
      T.PrepareTomatch.TomatchWithContextVector.make_return_pred_context
        (GlobalEnv.env env) sigma tomatches in
    let hypnaming = naming_of_program_mode MatchContext.program_mode in
    let _, return_pred_env =
      GlobalEnv.push_rel_context ~hypnaming sigma return_pred_context env in
    let* return_pred =
      match predopt with
      | Some term ->
          let* judgment = Typer.judgment_of_glob_constr return_pred_env term in
          let return_pred = EJudgment.uj_val judgment in
          return (ReturnPred.ReturnPred { return_pred;
            return_pred_height = Height.of_nat return_pred_height })
      | None -> return (ReturnPred.Tycon tycon) in
    let eqns =
      T.PrepareTomatch.TomatchWithContextVector.to_clauses env eqns tomatches in
    let tomatches =
      T.PrepareTomatch.TomatchWithContextVector.to_tomatch_vector tomatches in
    let return_pred =
      ReturnPred.morphism Refl eq_return_height return_pred in
    compile_loop { env; tomatches; return_pred; eqns }
end

let compile_cases ?loc ~(program_mode : bool) (style : Constr.case_style)
  ((typing_fun : compile_cases_typing_fun), (sigma : Evd.evar_map))
  (tycon : Evardefine.type_constraint) (env : GlobEnv.t)
    ((predopt : Glob_term.glob_constr option),
      (tomatchl : Glob_term.tomatch_tuples),
      (eqns : Glob_term.cases_clauses)) :
    Evd.evar_map * EConstr.unsafe_judgment =
  let open EvarMapMonad.Ops in
  let module Compiler = struct
    module rec Context : MatchContextS = struct
      let typing_fun = typing_fun
      let style = style
      let program_mode = program_mode
      let compile_loop = Compiler.compile_loop
    end
    and Compiler : CompilerS = Make (Context)
    include Compiler
  end in
  let env = Eq.cast (Eq.sym GlobalEnv.eq) env in
  let tycon = Option.map (Eq.cast (Eq.sym ETerm.eq)) tycon in
  let Exists eqns = Vector.of_list eqns in
  sigma |>
  let* judgment =
    Compiler.compile_cases ?tycon style env predopt tomatchl eqns in
  return (Eq.cast EJudgment.eq judgment)

let constr_of_pat :
           Environ.env ->
           Evd.evar_map ->
           EConstr.rel_context ->
           Glob_term.cases_pattern ->
           Names.Id.Set.t ->
           Evd.evar_map * Glob_term.cases_pattern *
           (EConstr.rel_context * EConstr.constr *
            (EConstr.types * EConstr.constr list) * Glob_term.cases_pattern) *
           Names.Id.Set.t =
    fun _ -> failwith "Not_implemented"

type 'a rhs =
    { rhs_env    : GlobEnv.t;
      rhs_vars   : Names.Id.Set.t;
      avoid_ids  : Names.Id.Set.t;
      it         : 'a option}

type 'a equation =
    { patterns     : Glob_term.cases_pattern list;
      rhs          : 'a rhs;
      alias_stack  : Names.Name.t list;
      eqn_loc      : Loc.t option;
      used         : bool ref }

type 'a matrix = 'a equation list

type tomatch_type =
  | IsInd of EConstr.types * Inductiveops.inductive_type * Names.Name.t list
  | NotInd of EConstr.constr option * EConstr.types

type tomatch_status =
  | Pushed of (bool*((EConstr.constr * tomatch_type) * int list * Names.Name.t))
  | Alias of
      (bool *
         (Names.Name.t * EConstr.constr * (EConstr.constr * EConstr.types)))
  | NonDepAlias
  | Abstract of int * EConstr.rel_declaration

type tomatch_stack = tomatch_status list

type pattern_history =
  | Top
  | MakeConstructor of Names.constructor * pattern_continuation

and pattern_continuation =
  | Continuation of int * Glob_term.cases_pattern list * pattern_history
  | Result of Glob_term.cases_pattern list

type 'a pattern_matching_problem =
    { env       : GlobEnv.t;
      pred      : EConstr.constr;
      tomatch   : tomatch_stack;
      history   : pattern_continuation;
      mat       : 'a matrix;
      caseloc   : Loc.t option;
      casestyle : Constr.case_style;
      typing_function: Evardefine.type_constraint -> GlobEnv.t -> Evd.evar_map -> 'a option -> Evd.evar_map * EConstr.unsafe_judgment }

let compile : program_mode:bool -> Evd.evar_map -> 'a pattern_matching_problem -> Evd.evar_map * EConstr.unsafe_judgment =
    fun ~program_mode _ -> failwith "Not_implemented"

let prepare_predicate : ?loc:Loc.t -> program_mode:bool ->
           (Evardefine.type_constraint ->
            GlobEnv.t -> Evd.evar_map -> Glob_term.glob_constr -> Evd.evar_map * EConstr.unsafe_judgment) ->
           GlobEnv.t ->
           Evd.evar_map ->
           (EConstr.types * tomatch_type) list ->
           EConstr.rel_context list ->
           EConstr.constr option -> Glob_term.glob_constr option -> (Evd.evar_map * (Names.Name.t * Names.Name.t list) list * EConstr.constr) list =
    fun ?loc ~program_mode _ -> failwith "Not_implemented"

let make_return_predicate_ltac_lvar : GlobEnv.t -> Evd.evar_map -> Names.Name.t ->
  Glob_term.glob_constr -> EConstr.constr -> GlobEnv.t =
    fun _ -> failwith "Not_implemented"
