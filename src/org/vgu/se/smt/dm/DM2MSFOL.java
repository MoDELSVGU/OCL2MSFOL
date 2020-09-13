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
import java.util.List;

import org.vgu.dm2schema.dm.Association;
import org.vgu.dm2schema.dm.Attribute;
import org.vgu.dm2schema.dm.DataModel;
import org.vgu.dm2schema.dm.Entity;
import org.vgu.se.smt.file.FileManager;

public class DM2MSFOL {

    private static class Template {
        public static String ENTITY = "(declare-fun %s (Classifier) Bool)";
        public static String ENTITY_1 = "(assert (not (%s nullClassifier)))";
        public static String ATTRIBUTE = "(declare-fun %s_%s (Classifier) %s)";
        public static String ASSOCIATION = "(declare-fun %s_%s (Classifier Classifier) Bool)";
        public static String ASSOCIATION_1 = "(assert (forall ((x Classifier))\r\n"
            + "    (forall ((y Classifier)) \r\n"
            + "        (=> (%s_%s x y) \r\n"
            + "            (and (%s x) (%s y))))))";
        public static String ENTITY_2 = "(assert (forall ((x Classifier)) \r\n"
            + "    (=> (%s x) (not %s))))";
    }

    public static DataModel dm;

    public static void setDataModel(DataModel dm_) {
        dm = dm_;
    }

    public static void map(FileManager fileManager) throws IOException {
        for (Entity e : dm.getEntities().values()) {
            fileManager.writeln(String.format(Template.ENTITY, e.getName()));
            fileManager.writeln(String.format(Template.ENTITY_1, e.getName()));
            for (Attribute at : e.getAttributes()) {
                fileManager.writeln(String.format(Template.ATTRIBUTE,
                    at.getName(), e.getName(),
                    at.getType().compareTo("String") == 0 ? "String" : "Int"));
            }
        }
        for (Association as : dm.getAssociations()) {
            fileManager.writeln(String.format(Template.ASSOCIATION,
                as.getLeftEnd(), as.getRightEnd()));
            fileManager.writeln(String.format(Template.ASSOCIATION_1,
                as.getLeftEnd(), as.getRightEnd(), as.getLeftEntityName(),
                as.getRightEntityName()));
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
                    .writeln(String.format(Template.ENTITY_2, e.getName(), s));
            } else {
                String s = "";
                for (Entity e_ : exclusion) {
                    s = s.concat(String.format(" (%s x)", e_.getName()));
                }
                String s_ = String.format("(or%s)", s);
                fileManager
                    .writeln(String.format(Template.ENTITY_2, e.getName(), s_));
            }
        }

    }
}
