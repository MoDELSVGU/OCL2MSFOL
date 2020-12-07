/**************************************************************************
Copyright 2020 Vietnamese-German-University

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

@author: ngpbh
***************************************************************************/

package org.vgu.se.smt.dm;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.vgu.dm2schema.dm.Association;
import org.vgu.dm2schema.dm.Attribute;
import org.vgu.dm2schema.dm.DataModel;
import org.vgu.dm2schema.dm.Entity;
import org.vgu.dm2schema.dm.Invariant;
import org.vgu.dm2schema.dm.Invariants;
import org.vgu.se.smt.file.FileManager;
import org.vgu.se.smt.ocl.OCL2MSFOL;

public class DM2MSFOL {

    private static class Template {
        public static String ENTITY = "(declare-fun %s (Classifier) Bool)";
        public static String ENTITY_1 = "(not (%s nullClassifier))";
        public static String ENTITY_1_BIS = "(not (%s invalidClassifier))";
        public static String ATTRIBUTE = "(declare-fun %s_%s (Classifier) %s)";
        public static String ATTRIBUTE_1 = "(= (%s_%s nullClassifier) invalid%s)";
        public static String ATTRIBUTE_1_BIS = "(= (%s_%s invalidClassifier) invalid%s)";
        public static String ATTRIBUTE_2 = "(forall ((x Classifier))\r\n"
            + "    (=> %s\r\n" + "        (distinct (%s_%s x) invalid%s)))";
        public static String ASSOCIATION = "(declare-fun %s_%s (Classifier Classifier) Bool)";
        public static String ASSOCIATION_1 = "(forall ((x Classifier))\r\n"
            + "    (forall ((y Classifier)) \r\n"
            + "        (=> (%s_%s x y) \r\n" + "            (and %s %s))))";
        public static String ENTITY_2 = "(forall ((x Classifier)) \r\n"
            + "    (=> (%s x) (not %s)))";
        public static String ENTITY_3 = "(declare-const %sType Type)";
        public static String ENTITY_3_BIS = "(distinct %sType %sType)";
        public static String ENTITY_4 = "(forall ((x Classifier))\r\n"
            + "    (and (=> (%1$s x)\r\n"
            + "             (OclIsTypeOf x %1$sType))\r\n"
            + "         (=> (OclIsTypeOf x %1$sType)\r\n"
            + "             (%1$s x))))";
        public static String ENTITY_5 = "(forall ((x Classifier))\r\n"
            + "    (and (=> %1$s\r\n"
            + "             (OclIsKindOf x %2$sType))\r\n"
            + "         (=> (OclIsKindOf x %2$sType)\r\n"
            + "             %1$s)))";
        public static String ASSOCIATION_2 = "(declare-fun %s_%s (Classifier) Classifier)";
        public static String ASSOCIATION_3 = "(= (%s_%s nullClassifier) invalidClassifier)";
        public static String ASSOCIATION_3_BIS = "(= (%s_%s invalidClassifier) invalidClassifier)";
        public static String ASSOCIATION_4 = "(forall ((x Classifier))\r\n"
            + "    (=> (%4$s x)\r\n"
            + "        (or (= (%1$s_%2$s x) nullClassifier)\r\n"
            + "            (%3$s (%1$s_%2$s x)))))";
        public static String ASSOCIATION_5 = "(forall ((x Classifier))\r\n"
            + "    (forall ((y Classifier))\r\n"
            + "        (=> (and (%1$s x)\r\n" + "                 (%2$s y)\r\n"
            + "                 (= (%2$s_%3$s y) x))\r\n"
            + "            (%1$s_%4$s x y))))";
        public static String ASSOCIATION_6 = "(forall ((x Classifier))\r\n"
            + "    (forall ((y Classifier))\r\n"
            + "        (=> (%1$s_%2$s x y)\r\n"
            + "            (= (%3$s_%4$s y) x))))";
    }

    public static DataModel dm;

    public static void setDataModel(DataModel dm_) {
        dm = dm_;
    }

    public static void map(FileManager fileManager) throws IOException {
        if (!fileManager.isSafeMode()) {
            fileManager
                .writeln("(declare-fun OclIsTypeOf (Classifier Type) Bool)");
            fileManager
                .writeln("(declare-fun OclIsKindOf (Classifier Type) Bool)");
        }
        for (Entity e : dm.getEntities().values()) {
            fileManager.writeln(String.format(Template.ENTITY, e.getName()));
            fileManager.assertln(String.format(Template.ENTITY_1, e.getName()));
            if (!fileManager.isSafeMode()) {
                fileManager
                    .writeln(String.format(Template.ENTITY_3, e.getName()));
            }
        }
        for (Entity e : dm.getEntities().values()) {
            if (!fileManager.isSafeMode())
                fileManager
                    .assertln(String.format(Template.ENTITY_1_BIS, e.getName()));
            for (Attribute at : e.getAttributes()) {
                fileManager.writeln(String.format(Template.ATTRIBUTE,
                    at.getName(), e.getName(),
                    at.getType().compareTo("String") == 0 ? "String" : "Int"));
                if (!fileManager.isSafeMode()) {
                    fileManager.assertln(String.format(Template.ATTRIBUTE_1,
                        at.getName(), e.getName(),
                        at.getType().compareTo("String") == 0 ? "String"
                            : "Int"));
                    fileManager.assertln(String.format(Template.ATTRIBUTE_1_BIS,
                        at.getName(), e.getName(),
                        at.getType().compareTo("String") == 0 ? "String"
                            : "Int"));
                    fileManager.assertln(String.format(Template.ATTRIBUTE_2,
                        getGeneralizationFormulae(e), at.getName(),
                        e.getName(),
                        at.getType().compareTo("String") == 0 ? "String"
                            : "Int"));
                }
            }
            if (!fileManager.isSafeMode()) {
                for (Entity _e : dm.getEntities().values()) {
                    if (e != _e) {
                        fileManager.assertln(String.format(Template.ENTITY_3_BIS,
                            e.getName(), _e.getName()));
                    }
                }
                fileManager
                    .assertln(String.format(Template.ENTITY_4, e.getName()));
                fileManager.assertln(String.format(Template.ENTITY_5,
                    getGeneralizationFormulae(e), e.getName()));
            }

        }
        for (Association as : dm.getAssociations()) {
            if (as.isManyToMany()) {
                fileManager.writeln(String.format(Template.ASSOCIATION,
                    as.getLeftEnd(), as.getRightEnd()));
                fileManager.assertln(String.format(Template.ASSOCIATION_1,
                    as.getLeftEnd(), as.getRightEnd(),
                    fileManager.isSafeMode()
                        ? String.format("(%s x)", as.getLeftEntityName())
                        : getGeneralizationFormulae(
                            dm.getEntities().get(as.getLeftEntityName())),
                    fileManager.isSafeMode()
                        ? String.format("(%s y)", as.getRightEntityName())
                        : getGeneralizationFormulae(
                            dm.getEntities().get(as.getRightEntityName()))));
            } else if (as.isManyToOne()) {
                fileManager.writeln(String.format(Template.ASSOCIATION_2,
                    as.getOneEnd().getCurrentClass(),
                    as.getOneEnd().getName()));
                fileManager.assertln(String.format(Template.ASSOCIATION_3,
                    as.getOneEnd().getCurrentClass(),
                    as.getOneEnd().getName()));
                fileManager.assertln(String.format(Template.ASSOCIATION_3_BIS,
                    as.getOneEnd().getCurrentClass(),
                    as.getOneEnd().getName()));
                fileManager.assertln(String.format(Template.ASSOCIATION_4,
                    as.getOneEnd().getCurrentClass(), as.getOneEnd().getName(),
                    as.getOneEnd().getTargetClass(),
                    as.getOneEnd().getCurrentClass()));
                fileManager.writeln(String.format(Template.ASSOCIATION,
                    as.getManyEnd().getCurrentClass(),
                    as.getManyEnd().getName()));
                fileManager.assertln(String.format(Template.ASSOCIATION_1,
                    as.getManyEnd().getCurrentClass(),
                    as.getManyEnd().getName(),
                    fileManager.isSafeMode()
                        ? String.format("(%s x)",
                            as.getManyEnd().getCurrentClass())
                        : getGeneralizationFormulae(dm.getEntities()
                            .get(as.getManyEnd().getCurrentClass())),
                    fileManager.isSafeMode()
                        ? String.format("(%s y)",
                            as.getManyEnd().getTargetClass())
                        : getGeneralizationFormulae(dm.getEntities()
                            .get(as.getManyEnd().getTargetClass()))));
                fileManager.assertln(String.format(Template.ASSOCIATION_5,
                    as.getManyEnd().getCurrentClass(),
                    as.getManyEnd().getTargetClass(), as.getManyEnd().getOpp(),
                    as.getManyEnd().getName()));
                fileManager.assertln(String.format(Template.ASSOCIATION_6,
                    as.getManyEnd().getCurrentClass(),
                    as.getManyEnd().getName(), as.getManyEnd().getTargetClass(),
                    as.getManyEnd().getOpp()));
            } else {
                // TODO: One to One
            }
        }
        for (Entity e : dm.getEntities().values()) {
            List<Entity> exclusion = new ArrayList<Entity>();
            for (Entity e_ : dm.getEntities().values()) {
                if (e_ != e) {
                    exclusion.add(e_);
                }
            }
            if (exclusion.isEmpty()) {
                break;
            } else if (exclusion.size() == 1) {
                String s = String.format("(%s x)", exclusion.get(0).getName());
                fileManager
                    .assertln(String.format(Template.ENTITY_2, e.getName(), s));
            } else {
                String s = "";
                for (Entity e_ : exclusion) {
                    s = s.concat(String.format(" (%s x)", e_.getName()));
                }
                String s_ = String.format("(or%s)", s);
                fileManager
                    .assertln(String.format(Template.ENTITY_2, e.getName(), s_));
            }
        }
        
        OCL2MSFOL.setDataModel(dm);
        
        for (Invariants invs : dm.getInvariants()) {
            for(Invariant inv : invs) {
                String invLabel = inv.getLabel();
                String invOcl = inv.getOcl();
                System.out.println(invLabel);
                System.out.println(invOcl);
                OCL2MSFOL.setExpression(invOcl);
                fileManager.commentln(invLabel);
                OCL2MSFOL.map(fileManager);
            }
        }
    }

    private static String getGeneralizationFormulae(Entity e) {
        Set<Entity> superClasses = new HashSet<Entity>(getSubClasses(e));
        if (superClasses.isEmpty()) {
            return String.format("(%s x)", e.getName());
        } else {
            String s = "(or %s)";
            String firstClass = String.format("(%s x)", e.getName());
            for (Entity e_ : superClasses) {
                firstClass = firstClass
                    .concat(String.format(" (%s x)", e_.getName()));
            }
            return String.format(s, firstClass);
        }
    }

    private static List<Entity> getSubClasses(Entity e) {
        List<Entity> results = new ArrayList<Entity>();
        for (Entity _e : dm.getEntities().values()) {
            if (isSuperClass(e, _e)) {
                results.add(_e);
            }
        }
        return results;
    }

    private static boolean isSuperClass(Entity e, Entity _e) {
        if (_e.getName() == e.getName())
            return false;
        if (_e.getSuperClass() == null) {
            return false;
        }
        if (_e.getSuperClass().getName() != e.getName()) {
            return isSuperClass(e, _e.getSuperClass());
        }
        return true;
    }
}
