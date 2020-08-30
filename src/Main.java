import net.sf.jsqlparser.JSQLParserException;
import net.sf.jsqlparser.parser.CCJSqlParserUtil;
import net.sf.jsqlparser.statement.Statement;

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

public class Main {
    public static void main (String[] args) throws JSQLParserException {
        Statement stmt = CCJSqlParserUtil.parse("SELECT CASE WHEN (EXISTS (SELECT * FROM Student WHERE age <= 18)) THEN 1 ELSE 0 END");
        System.out.println(stmt);
    }
}
