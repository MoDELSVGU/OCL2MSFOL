(set-logic UFSLIA)
(set-option :produce-models true)

(declare-sort Classifier 0)
(declare-const nullClassifier Classifier)

(declare-const nullInteger Int)

(declare-const nullString String)

(declare-fun student (Classifier) Bool)
(declare-fun lecturer (Classifier) Bool)

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

; SELECT EXISTS (SELECT * FROM Student AS x WHERE x.age <= 18)
(assert (exists ((x Classifier)) 
    (and (student x) (not (= (age_Student x) nullInteger)) (<= (age_Student x) 18))))

; SELECT NOT EXISTS (SELECT * FROM Student AS x WHERE x.age <= 18)
(assert (forall ((x Classifier)) 
    (=> (student x) (and (not (= (age_Student x) nullInteger)) (not (<= (age_Student x) 18))))))

(check-sat)