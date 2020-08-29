(set-logic UFSLIA)
(set-option :produce-models true)

(declare-sort Classifier 0)
(declare-const nullClassifier Classifier)

(declare-const nullInteger Int)

(declare-const nullString String)

(declare-const _self Classifier)
(declare-const _caller Classifier)

(declare-fun student (Classifier) Bool)
(declare-fun lecturer (Classifier) Bool)

(assert (lecturer _self))
(assert (lecturer _caller))

(declare-fun name_Student (Classifier) String)

(declare-fun age_Student (Classifier) Int)

(declare-fun name_Lecturer (Classifier) String)

(declare-fun students_lecturers (Classifier Classifier) Bool)

(assert (forall ((x Classifier)) 
    (=> (student x) (not (lecturer x)))))

(assert (not (student nullClassifier)))

(assert (forall ((x Classifier))
    (=> (lecturer x) (not (student x)))))

(assert (not (lecturer nullClassifier)))

(assert (forall ((x Classifier))(forall ((y Classifier))
    (=> (students_lecturers x y) (and (student x) (lecturer y))))))

; Student.allInstances()->forAll(p|p.age > 18)
(assert (forall ((x Classifier)) 
    (=> (student x) (and (> (age_Student x) 18) (not (= (age_Student x) nullInteger))))))

; Student.allInstances()->exists(p|p.age <= 18)
;(assert (exists ((x Classifier)) 
;    (and (student x) (and (<= (age_Student x) 18) (not (= (age_Student x) nullInteger))))))

; Student.allInstances()->exists(p|p.age.oclIsUndefined())
(assert (exists ((x Classifier)) 
    (and (student x) (= (age_Student x) nullInteger))))

; _self.students->includes(_caller)
(assert (exists ((x Classifier)) 
    (and (students_lecturers x _self) (= x _caller))))

(check-sat)
;(get-model)
