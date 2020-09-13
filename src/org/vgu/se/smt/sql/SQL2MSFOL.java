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

package org.vgu.se.smt.sql;

import java.util.HashMap;

public class SQL2MSFOL {
    private static HashMap<String, Expression> maps = new HashMap<String, Expression>();

    public static Expression map(String key) {
        return maps.get(key);
    }

    public static void clear() {
        maps.clear();
    }

    public static void add(String key, Expression e) {
        maps.put(key, e);
    }

    public static void print() {
        for (String k : maps.keySet()) {
            System.out
                .println(String.format("Key: %1$s, Exp: %2$s", k, maps.get(k).toString()));
        }
    }

}
