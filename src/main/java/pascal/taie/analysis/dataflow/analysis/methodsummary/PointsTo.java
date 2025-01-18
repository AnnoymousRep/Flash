package pascal.taie.analysis.dataflow.analysis.methodsummary;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.language.type.TypeSystem;

public class PointsTo {

    private Contr mergedContr;

    private TypeSystem typeSystem = World.get().getTypeSystem();

    public PointsTo() {
    }

    public static PointsTo make() {
        return new PointsTo();
    }

    public boolean add(Contr contr) { // 简单实现了merge策略
        if (contr == null) return false;
        if (mergedContr == null) {
            mergedContr = contr;
            return true;
        } else {
            if (mergedContr.isNew() && contr.isNew()) {
                if ((typeSystem.isSubtype(contr.getType(), mergedContr.getType()) && !mergedContr.getType().equals(contr.getType()))
                        || (ContrUtil.isControllable(contr) && !ContrUtil.isControllable(mergedContr))) {
                    mergedContr = contr;
                    return true;
                } else if (!typeSystem.isSubtype(mergedContr.getType(), contr.getType())) {
                    mergedContr.addNewType(contr.getType()); // 处理两个无继承关系的new对象
                    return true;
                }
            } else if (ContrUtil.needUpdateInMerge(mergedContr.getValue(), contr.getValue())) {
                mergedContr = contr;
                return true;
            }
        }
        return false;
    }

    public void add(PointsTo pointsTo) {
        add(pointsTo.getMergedContr());
    }

    public Contr getMergedContr() {
        return mergedContr;
    }

    public boolean isEmpty() {
        return mergedContr == null;
    }

    public void setValue(String s) {
        mergedContr.setValue(s);
    }
}
