(set-logic UFSLIA)
(set-option :produce-models true)
(declare-sort Classifier 0)
(declare-sort Type 0)
(declare-const nullClassifier Classifier)
(declare-const invalidClassifier Classifier)
(declare-const nullInt Int)
(declare-const invalidInt Int)
(declare-const nullString String)
(declare-const invalidString String)
(assert (distinct nullClassifier invalidClassifier))
(assert (distinct nullInt invalidInt))
(assert (distinct nullString invalidString))
(declare-fun OclIsTypeOf (Classifier Type) Bool)
(declare-fun OclIsKindOf (Classifier Type) Bool)
(declare-fun Lecturer (Classifier) Bool)
(assert (not (Lecturer nullClassifier)))
(declare-const LecturerType Type)
(declare-fun Student (Classifier) Bool)
(assert (not (Student nullClassifier)))
(declare-const StudentType Type)
(assert (not (Lecturer invalidClassifier)))
(declare-fun email_Lecturer (Classifier) String)
(assert (= (email_Lecturer nullClassifier) invalidString))
(assert (= (email_Lecturer invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Lecturer x)
        (distinct (email_Lecturer x) invalidString))))
(declare-fun age_Lecturer (Classifier) Int)
(assert (= (age_Lecturer nullClassifier) invalidInt))
(assert (= (age_Lecturer invalidClassifier) invalidInt))
(assert (forall ((x Classifier))
    (=> (Lecturer x)
        (distinct (age_Lecturer x) invalidInt))))
(assert (distinct LecturerType StudentType))
(assert (forall ((x Classifier))
    (and (=> (Lecturer x)
             (OclIsTypeOf x LecturerType))
         (=> (OclIsTypeOf x LecturerType)
             (Lecturer x)))))
(assert (forall ((x Classifier))
    (and (=> (Lecturer x)
             (OclIsKindOf x LecturerType))
         (=> (OclIsKindOf x LecturerType)
             (Lecturer x)))))
(assert (not (Student invalidClassifier)))
(declare-fun email_Student (Classifier) String)
(assert (= (email_Student nullClassifier) invalidString))
(assert (= (email_Student invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Student x)
        (distinct (email_Student x) invalidString))))
(assert (distinct StudentType LecturerType))
(assert (forall ((x Classifier))
    (and (=> (Student x)
             (OclIsTypeOf x StudentType))
         (=> (OclIsTypeOf x StudentType)
             (Student x)))))
(assert (forall ((x Classifier))
    (and (=> (Student x)
             (OclIsKindOf x StudentType))
         (=> (OclIsKindOf x StudentType)
             (Student x)))))
(declare-fun Enrollment (Classifier Classifier) Bool)
(assert (forall ((x Classifier))
    (forall ((y Classifier)) 
        (=> (Enrollment x y) 
            (and (Lecturer x) (Student x))))))
(assert (forall ((x Classifier)) 
    (=> (Lecturer x) (not (Student x)))))
(assert (forall ((x Classifier)) 
    (=> (Student x) (not (Lecturer x)))))
(assert (forall ((l1 Classifier))
    (and (=> (Lecturer l1) 
                (forall ((l2 Classifier))
                    (and (=> (Lecturer l2) 
                             (or (and (= (age_Lecturer l1) nullInt) 
                                      (= (age_Lecturer l2) nullInt)) 
                                 (and (= (age_Lecturer l1) (age_Lecturer l2)) 
                                      (not (or (= (age_Lecturer l1) nullInt) 
                                               (or (= l1 nullClassifier) 
                                                   (= l1 invalidClassifier)) 
                                               (= (age_Lecturer l2) nullInt) 
                                               (or (= l2 nullClassifier) 
                                                   (= l2 invalidClassifier))))))) 
                         (not false)))) 
         (not false))))
(check-sat)
