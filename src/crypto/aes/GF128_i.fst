module GF128_i

let lemma_gf128_degree () =
  lemma_add_define_all ();
  lemma_monomial_define 128;
  lemma_of_list_degree [true; true; true; false; false; false; false; true];
  lemma_degree_is (monomial 128) 128;
  lemma_degree_is gf128_modulus 128;
  ()

let lemma_gf128_mul a b c d n =
  let ab = a *. n +. b in
  let cd = c *. n +. d in
  let ac = a *. c in
  let ad = a *. d in
  let bc = b *. c in
  let bd = b *. d in
  let ach = ac /. n in
  let adh = ad /. n in
  let bch = bc /. n in
  let bdh = bd /. n in
  let acl = ac %. n in
  let adl = ad %. n in
  let bcl = bc %. n in
  let bdl = bd %. n in
  // ab *. cd
  // (a *. n +. b) *. (c *. n +. d)
  lemma_mul_distribute_right (a *. n +. b) (c *. n) d;
  lemma_mul_distribute_left (a *. n) b (c *. n);
  lemma_mul_distribute_left (a *. n) b d;
  // ((a *. n) *. (c *. n) +. b *. (c *. n)) +. ((a *. n) *. d +. b *. d);
  lemma_mul_associate b c n;
  lemma_mul_associate a n d;
  lemma_mul_commute n d;
  lemma_mul_associate a d n;
  lemma_mul_associate a n (c *. n);
  lemma_mul_associate n c n;
  lemma_mul_commute c n;
  lemma_mul_associate c n n;
  lemma_mul_associate a c (n *. n);
  // (ac *. (n *. n) +. bc *. n) +. (ad *. n +. bd)
  lemma_div_mod ac n;
  lemma_div_mod ad n;
  lemma_div_mod bc n;
  lemma_div_mod bd n;
  // ((ach *. n +. acl) *. (n *. n) +. (bch *. n +. bcl) *. n) +. ((adh *. n +. adl) *. n +. (bdh *. n +. bdl))
  lemma_mul_distribute_left (ach *. n) acl (n *. n);
  lemma_mul_distribute_left (bch *. n) bcl n;
  lemma_mul_distribute_left (adh *. n) adl n;
  // (((ach *. n) *. (n *. n) +. acl *. (n *. n)) +. (bch *. n *. n +. bcl *. n)) +. ((adh *. n *. n +. adl *. n) +. (bdh *. n +. bdl))
  lemma_mul_associate bch n n;
  lemma_mul_associate adh n n;
  // ((((ach *. n) *. (n *. n)) +. acl *. (n *. n)) +. (bch *. (n *. n) +. bcl *. n)) +. ((adh *. (n *. n) +. adl *. n) +. (bdh *. n +. bdl))
  assert (ab *. cd == ((((ach *. n) *. (n *. n)) +. acl *. (n *. n)) +. (bch *. (n *. n) +. bcl *. n)) +. ((adh *. (n *. n) +. adl *. n) +. (bdh *. n +. bdl)));
  lemma_add_define_all ();
  lemma_equal (ab *. cd) (((ach *. n) *. (n *. n) +. (acl *. (n *. n) +. bch *. (n *. n) +. adh *. (n *. n))) +. (bcl *. n +. adl *. n +. bdh *. n +. bdl));
  // ((ach *. n) *. (n *. n) +. (acl *. (n *. n) +. bch *. (n *. n) +. adh *. (n *. n))) +. (bcl *. n +. adl *. n +. bdh *. n +. bdl)
  lemma_mul_distribute_left acl bch (n *. n);
  lemma_mul_distribute_left (acl +. bch) adh (n *. n);
  lemma_mul_distribute_left bcl adl n;
  lemma_mul_distribute_left (bcl +. adl) bdh n;
  lemma_mul_distribute_left (ach *. n) (acl +. bch +. adh) (n *. n);
  // ((ach *. n) +. (acl +. bch +. adh)) *. (n *. n) +. ((bcl +. adl +. bdh) *. n +. bdl)
  ()

let lemma_gf128_reduce a b g n h =
  let ab = a *. b in
  let d = ab /. n in
  let m = ab %. n in
  let dh = d *. h in
  let d' = dh /. n in
  let m' = dh %. n in
  lemma_div_mod ab n;
  lemma_div_mod dh n;
  lemma_div_degree ab n;
  lemma_mod_degree ab n;
  lemma_div_degree dh n;
  lemma_mod_degree dh n;
  lemma_mul_degree a b;
  lemma_mul_degree d' h;
  lemma_mul_degree d h;
  // ab == d *. n +. m
  // dh == d' *. n +. m'

  // ab % g
  // (d *. n +. m) % g
  lemma_add_define_all ();
  lemma_zero_define ();
  lemma_equal n (g +. h);
  // (d *. (g +. h) +. m) % g
  lemma_mul_distribute_right d g h;
  // (d *. g +. dh +. m) % g
  // (d *. g +. (d' *. n +. m') + m) % g
  // (d *. g +. (d' *. (g +. h) +. m') + m) % g
  lemma_mul_distribute_right d' g h;
  // (d *. g +. (d' *. g +. d' *. h +. m') + m) % g
  lemma_equal ab ((d *. g +. d' *. g) +. (d' *. h +. m' +. m));
  lemma_mul_distribute_left d d' g;
  // ((d +. d') *. g +. (d' *. h +. m' +. m)) % g
  lemma_mod_distribute ((d +. d') *. g) (d' *. h +. m' +. m) g;
  lemma_div_mod_exact (d +. d') g;
  lemma_equal (ab %. g) ((d' *. h +. m' +. m) %. g);
  // (d' *. h +. m' +. m) % g
  lemma_add_degree (d' *. h) m';
  lemma_add_degree (d' *. h +. m') m;
  lemma_mod_small (d' *. h +. m' +. m) g;
  // d' *. h +. m' +. m
  ()
