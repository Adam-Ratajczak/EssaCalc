;;; Compiled by f2cl version:
;;; ("f2cl1.l,v 46c1f6a93b0d 2012/05/03 04:40:28 toy $"
;;;  "f2cl2.l,v 96616d88fb7e 2008/02/22 22:19:34 rtoy $"
;;;  "f2cl3.l,v 96616d88fb7e 2008/02/22 22:19:34 rtoy $"
;;;  "f2cl4.l,v 96616d88fb7e 2008/02/22 22:19:34 rtoy $"
;;;  "f2cl5.l,v 46c1f6a93b0d 2012/05/03 04:40:28 toy $"
;;;  "f2cl6.l,v 1d5cbacbb977 2008/08/24 00:56:27 rtoy $"
;;;  "macros.l,v fceac530ef0c 2011/11/26 04:02:26 toy $")

;;; Using Lisp CMU Common Lisp snapshot-2012-04 (20C Unicode)
;;; 
;;; Options: ((:prune-labels nil) (:auto-save t) (:relaxed-array-decls t)
;;;           (:coerce-assigns :as-needed) (:array-type ':simple-array)
;;;           (:array-slicing nil) (:declare-common nil)
;;;           (:float-format double-float))

(in-package :slatec)


(let ((ntae10 0)
      (ntae11 0)
      (ntae12 0)
      (nte11 0)
      (nte12 0)
      (ntae13 0)
      (ntae14 0)
      (xmax 0.0)
      (ae10cs
       (make-array 50
                   :element-type 'double-float
                   :initial-contents '(0.03284394579616699
                                       -0.016699204520313628
                                       2.845284724361347e-4
                                       -7.563944358516206e-6
                                       2.7989712894508593e-7
                                       -1.357901828534531e-8
                                       8.343596202040469e-10
                                       -6.370971727640248e-11
                                       6.007247608811861e-12
                                       -7.022876174679774e-13
                                       1.0183026737036877e-13
                                       -1.7618129034308802e-14
                                       3.2508286142353605e-15
                                       -5.071770025505819e-16
                                       1.6651773870432943e-17
                                       3.1667538907975144e-17
                                       -1.5884037636641416e-17
                                       4.175513256138019e-18
                                       -2.8923477497071417e-19
                                       -2.800625903396608e-19
                                       1.322938639539271e-19
                                       -1.8044474441773015e-20
                                       -7.905384086522615e-21
                                       4.43571136636957e-21
                                       -4.26410399497812e-22
                                       -3.9201017669371173e-22
                                       1.5273780513439943e-22
                                       1.0248495270493723e-23
                                       -2.1349078747714336e-23
                                       3.239139475160028e-24
                                       2.14218376229989e-24
                                       -8.234609419601019e-25
                                       -1.5246528296458095e-25
                                       1.378208282460639e-25
                                       2.1313112028339478e-27
                                       -2.012649651526484e-26
                                       1.995535662263358e-27
                                       2.7989958089840034e-27
                                       -5.534511845389627e-28
                                       -3.884995396159969e-28
                                       1.1213044345073594e-28
                                       5.566568152423741e-29
                                       -2.0454829298104996e-29
                                       -8.453813992712336e-30
                                       3.5657584334312916e-30
                                       1.3836538721256348e-30
                                       -6.0621678644513725e-31
                                       -2.4471980439893134e-31
                                       1.0068506409339983e-31
                                       4.623685555014869e-32)))
      (ae11cs
       (make-array 60
                   :element-type 'double-float
                   :initial-contents '(0.2026315064707889 -0.07365514099120313
                                       0.006390934911836192
                                       -6.079725270524792e-4
                                       -7.370649862017663e-5
                                       4.873285744945018e-5
                                       -2.383706484044829e-6
                                       -3.051861262856152e-6
                                       1.705033157256456e-7
                                       2.3834204527487747e-7
                                       1.0781772556163167e-8
                                       -1.7955692847399104e-8
                                       -4.128407234195046e-9
                                       6.862214858863197e-10
                                       5.313018312050636e-10
                                       7.87968802614907e-11
                                       -2.626176232935652e-11
                                       -1.5483687636308263e-11
                                       -2.581896237726139e-12
                                       5.954287919159107e-13
                                       4.645140038768153e-13
                                       1.155785502325586e-13
                                       -1.0475236870835799e-15
                                       -1.1896653502709005e-14
                                       -4.774907749026178e-15
                                       -8.107764961577278e-16
                                       1.3435569250031553e-16
                                       1.4134530022913106e-16
                                       4.9451592573953175e-17
                                       7.988404848008067e-18
                                       -1.400863218808981e-18
                                       -1.4814246958417373e-18
                                       -5.58261736460256e-19
                                       -1.1442074542191647e-19
                                       2.537182387956685e-21
                                       1.320532815480536e-20
                                       6.293026108158681e-21
                                       1.7688270424882712e-21
                                       2.3266187985146046e-22
                                       -6.780306081112523e-23
                                       -5.944087695967637e-23
                                       -2.3618214531184416e-23
                                       -6.0214499724601476e-24
                                       -6.55179064743483e-25
                                       2.9388755297497726e-25
                                       2.2601606200642114e-25
                                       8.953436924595863e-26
                                       2.4015923471098456e-26
                                       3.4118376888907176e-27
                                       -7.161707169463034e-28
                                       -7.562039065928173e-28
                                       -3.3774612157467327e-28
                                       -1.047932570330094e-28
                                       -2.1654550252170343e-29
                                       -7.529712574528827e-31
                                       1.9103179392798935e-30
                                       1.1492104966530338e-30
                                       4.389697058266175e-31
                                       1.2320883239205687e-31
                                       2.2220174457553174e-32)))
      (ae12cs
       (make-array 41
                   :element-type 'double-float
                   :initial-contents '(0.6362958979674704 -0.13081168675067634
                                       -0.008436741021305393
                                       0.0026568491531006686
                                       3.2822721781658134e-4
                                       -2.3783447771430248e-5
                                       -1.1439804308100055e-5
                                       -1.4405943433238338e-6
                                       5.241595665114883e-9
                                       3.8407306407844325e-8
                                       8.58802448602672e-9
                                       1.0219226625855004e-9
                                       2.1749132323289725e-11
                                       -2.2090238142623143e-11
                                       -6.3457533544928755e-12
                                       -1.083774656685766e-12
                                       -1.1909822872222587e-13
                                       -2.8438682389265592e-15
                                       2.508032702668677e-15
                                       7.872964152855985e-16
                                       1.5475066347785216e-16
                                       2.2575322831665076e-17
                                       2.223335286726661e-18
                                       1.6967819563544153e-20
                                       -5.760831625594768e-20
                                       -1.7591235774646877e-20
                                       -3.628605637510317e-21
                                       -5.923556979732899e-22
                                       -7.603038092631019e-23
                                       -6.254784352171177e-24
                                       2.548336075930765e-25
                                       2.5598615731739856e-25
                                       7.137623935789932e-26
                                       1.4703759939567568e-26
                                       2.5105524765386733e-27
                                       3.588666638779089e-28
                                       3.98860351567713e-29
                                       2.176367694735622e-30
                                       -4.614699848761894e-31
                                       -2.071351787748199e-31
                                       -5.189037856353437e-32)))
      (e11cs
       (make-array 29
                   :element-type 'double-float
                   :initial-contents '(-16.113461655571495 7.79407277874268
                                       -1.955405818863142 0.37337293866277943
                                       -0.05692503191092902
                                       0.0072110777696600915
                                       -7.810490144984159e-4
                                       7.388093356262168e-5
                                       -6.202861875808204e-6
                                       4.6816002303176734e-7
                                       -3.209288853329865e-8
                                       2.0151997487404535e-9
                                       -1.1673686816697794e-10
                                       6.276270667203995e-12
                                       -3.148154167227544e-13
                                       1.4799041744493474e-14
                                       -6.545709158397967e-16
                                       2.733687222313729e-17
                                       -1.0813524349754407e-18
                                       4.06283280404343e-20
                                       -1.4535539358960456e-21
                                       4.9632746181648634e-23
                                       -1.6208612696636044e-24
                                       5.072144803860742e-26
                                       -1.5235811133372208e-27
                                       4.400151125610362e-29
                                       -1.2236141945416232e-30
                                       3.2809216661066004e-32
                                       -8.493345226830644e-34)))
      (e12cs
       (make-array 25
                   :element-type 'double-float
                   :initial-contents '(-0.037390214792202794
                                       0.042723986062209576
                                       -0.13031820798497004 0.01441912402469889
                                       -0.0013461707805106802
                                       1.073102925306378e-4
                                       -7.429999516119436e-6
                                       4.537732569075371e-7
                                       -2.4764172113906014e-8
                                       1.2207658137459096e-9
                                       -5.485141480640924e-11
                                       2.263621421300788e-12
                                       -8.63589727169801e-14
                                       3.06291553669333e-15
                                       -1.0148571885594415e-16
                                       3.1548217403406988e-18
                                       -9.23604240769241e-20
                                       2.55504267970814e-21
                                       -6.699128056845668e-23
                                       1.6692540543538733e-24
                                       -3.9625492518437966e-26
                                       8.981358965985113e-28
                                       -1.9476336699301643e-29
                                       4.0483601902463e-31
                                       -8.079815676998451e-33)))
      (ae13cs
       (make-array 50
                   :element-type 'double-float
                   :initial-contents '(-0.6057732466406035 -0.1125352434836609
                                       0.01343226624790278
                                       -0.0019268451873811457
                                       3.091183377206032e-4
                                       -5.356413212961842e-5
                                       9.827812880247493e-6
                                       -1.8853689849165184e-6
                                       3.7494319356894736e-7
                                       -7.682345587055264e-8
                                       1.6143270567198776e-8
                                       -3.4668022114907356e-9
                                       7.587542091903628e-10
                                       -1.6886433329881412e-10
                                       3.8145706749552266e-11
                                       -8.733026632444629e-12
                                       2.023672864586796e-12
                                       -4.741328303955583e-13
                                       1.1221172048389864e-13
                                       -2.680422543484031e-14
                                       6.457851441771653e-15
                                       -1.5682760501666479e-15
                                       3.8367865399315405e-16
                                       -9.451717302757913e-17
                                       2.3434812288949573e-17
                                       -5.845866158021471e-18
                                       1.4666229867947778e-18
                                       -3.6993923476444474e-19
                                       9.379015993672124e-20
                                       -2.3893673221937873e-20
                                       6.115062462949761e-21
                                       -1.5718585327554025e-21
                                       4.0572387285585398e-22
                                       -1.0514026554738035e-22
                                       2.734966493063867e-23
                                       -7.14016040802058e-24
                                       1.870555243223508e-24
                                       -4.916746816687048e-25
                                       1.2964988119684032e-25
                                       -3.4292515688362866e-26
                                       9.097224164388703e-27
                                       -2.4202112314316855e-27
                                       6.4563612934639515e-28
                                       -1.7269132735340542e-28
                                       4.6308611659151503e-29
                                       -1.2448703637214132e-29
                                       3.354457409052068e-30
                                       -9.059886852107077e-31
                                       2.4524147051474238e-31
                                       -6.652817873355206e-32)))
      (ae14cs
       (make-array 64
                   :element-type 'double-float
                   :initial-contents '(-0.1892918000753017 -0.08648117855259871
                                       0.007224101543746595
                                       -8.097559457557386e-4
                                       1.0999134432661389e-4
                                       -1.7173329989377674e-5
                                       2.9856275144792833e-6
                                       -5.65964914577193e-7 1.15268083971414e-7
                                       -2.4950304402693382e-8
                                       5.692324201833754e-9
                                       -1.3599576648056003e-9
                                       3.3846628887608844e-10
                                       -8.737853904474682e-11
                                       2.33158866322266e-11
                                       -6.411481049213786e-12
                                       1.8122469802048165e-12
                                       -5.253831761558461e-13
                                       1.5592182725919257e-13
                                       -4.7291682970803986e-14
                                       1.4637618643932435e-14
                                       -4.617388988712924e-15
                                       1.4827103482893693e-15
                                       -4.841672496239229e-16
                                       1.6062155757002903e-16
                                       -5.408917538957171e-17
                                       1.847470159346898e-17
                                       -6.395830792759095e-18
                                       2.2427807216997594e-18
                                       -7.961369173983947e-19
                                       2.8593081115401974e-19
                                       -1.0384502447011372e-19
                                       3.8120406070979756e-20
                                       -1.4137954177172008e-20
                                       5.295367865182741e-21
                                       -2.002264245026826e-21
                                       7.640262751275196e-22
                                       -2.941119006868788e-22
                                       1.1418235390789271e-22
                                       -4.4693084759552986e-23
                                       1.7632624105717507e-23
                                       -7.009968187925902e-24
                                       2.807573556558379e-24
                                       -1.1325609449810865e-24
                                       4.600574684375018e-25
                                       -1.8814485989761335e-25
                                       7.744916111507731e-26
                                       -3.208512760585369e-26
                                       1.3374455429108399e-26
                                       -5.608671881802217e-27
                                       2.3658397165285374e-27
                                       -1.0036561950253053e-27
                                       4.281490878094161e-28
                                       -1.836345261815318e-28
                                       7.91779823134954e-29
                                       -3.4315423587422206e-29
                                       1.4947054938971032e-29
                                       -6.542620279865706e-30
                                       2.8775813951991712e-30
                                       -1.2715572117960247e-30
                                       5.644615555648722e-31
                                       -2.5169949942840953e-31
                                       1.1272598189275103e-31
                                       -5.069814875800461e-32)))
      (first$ nil))
  (declare (type (f2cl-lib:integer4) ntae10 ntae11 ntae12 nte11 nte12 ntae13
                                     ntae14)
           (type (double-float) xmax)
           (type (simple-array double-float (50)) ae10cs ae13cs)
           (type (simple-array double-float (60)) ae11cs)
           (type (simple-array double-float (41)) ae12cs)
           (type (simple-array double-float (29)) e11cs)
           (type (simple-array double-float (25)) e12cs)
           (type (simple-array double-float (64)) ae14cs)
           (type f2cl-lib:logical first$))
  (setq first$ f2cl-lib:%true%)
  (defun de1 (x)
    (declare (type (double-float) x))
    (prog ((xmaxt 0.0) (de1 0.0) (eta 0.0f0))
      (declare (type (single-float) eta) (type (double-float) de1 xmaxt))
      (cond
        (first$
         (setf eta (* 0.1f0 (f2cl-lib:freal (f2cl-lib:d1mach 3))))
         (setf ntae10 (initds ae10cs 50 eta))
         (setf ntae11 (initds ae11cs 60 eta))
         (setf ntae12 (initds ae12cs 41 eta))
         (setf nte11 (initds e11cs 29 eta))
         (setf nte12 (initds e12cs 25 eta))
         (setf ntae13 (initds ae13cs 50 eta))
         (setf ntae14 (initds ae14cs 64 eta))
         (setf xmaxt (- (f2cl-lib:flog (f2cl-lib:d1mach 1))))
         (setf xmax (- xmaxt (f2cl-lib:flog xmaxt)))))
      (setf first$ f2cl-lib:%false%)
      (if (> x -1.0) (go label50))
      (if (> x -32.0) (go label20))
      (setf de1
              (* (/ (exp (- x)) x)
                 (+ 1.0 (dcsevl (+ (/ 64.0 x) 1.0) ae10cs ntae10))))
      (go end_label)
     label20
      (if (> x -8.0) (go label30))
      (setf de1
              (* (/ (exp (- x)) x)
                 (+ 1.0 (dcsevl (/ (+ (/ 64.0 x) 5.0) 3.0) ae11cs ntae11))))
      (go end_label)
     label30
      (if (> x -4.0) (go label40))
      (setf de1
              (* (/ (exp (- x)) x)
                 (+ 1.0 (dcsevl (+ (/ 16.0 x) 3.0) ae12cs ntae12))))
      (go end_label)
     label40
      (setf de1
              (- (dcsevl (/ (+ (* 2.0 x) 5.0) 3.0) e11cs nte11)
                 (f2cl-lib:flog (- x))))
      (go end_label)
     label50
      (if (> x 1.0) (go label60))
      (if (= x 0.0) (xermsg "SLATEC" "DE1" "X IS 0" 2 2))
      (setf de1
              (+ (- -0.6875 (f2cl-lib:flog (abs x))) x (dcsevl x e12cs nte12)))
      (go end_label)
     label60
      (if (> x 4.0) (go label70))
      (setf de1
              (* (/ (exp (- x)) x)
                 (+ 1.0 (dcsevl (/ (- (/ 8.0 x) 5.0) 3.0) ae13cs ntae13))))
      (go end_label)
     label70
      (if (> x xmax) (go label80))
      (setf de1
              (* (/ (exp (- x)) x)
                 (+ 1.0 (dcsevl (- (/ 8.0 x) 1.0) ae14cs ntae14))))
      (go end_label)
     label80
      (xermsg "SLATEC" "DE1" "X SO BIG E1 UNDERFLOWS" 1 1)
      (setf de1 0.0)
      (go end_label)
     end_label
      (return (values de1 nil)))))

(in-package #:cl-user)
#+#.(cl:if (cl:find-package '#:f2cl) '(and) '(or))
(eval-when (:load-toplevel :compile-toplevel :execute)
  (setf (gethash 'fortran-to-lisp::de1 fortran-to-lisp::*f2cl-function-info*)
          (fortran-to-lisp::make-f2cl-finfo :arg-types '((double-float))
                                            :return-values '(nil)
                                            :calls '(fortran-to-lisp::xermsg
                                                     fortran-to-lisp::dcsevl
                                                     fortran-to-lisp::initds
                                                     fortran-to-lisp::d1mach))))

