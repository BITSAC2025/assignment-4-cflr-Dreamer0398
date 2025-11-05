/**
 * CFLR.cpp
 * @author kisslune 
 */

#include "A4Header.h"

using namespace SVF;
using namespace llvm;
using namespace std;

int main(int argc, char **argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVFIRBuilder builder;
    auto pag = builder.build();
    pag->dump();

    CFLR solver;
    solver.buildGraph(pag);
    // TODO: complete this method
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    // 初始化工作列表：将所有已存在的边加入工作列表
    auto &succMap = graph->getSuccessorMap();
    for (auto &nodeItr : succMap)
    {
        unsigned src = nodeItr.first;
        for (auto &lblItr : nodeItr.second)
        {
            EdgeLabel label = lblItr.first;
            for (auto dst : lblItr.second)
            {
                workList.push(CFLREdge(src, dst, label));
            }
        }
    }

    // 动态规划算法：处理工作列表直到为空
    while (!workList.empty())
    {
        CFLREdge edge = workList.pop();
        unsigned src = edge.src;
        unsigned dst = edge.dst;
        EdgeLabel label = edge.label;

        // 根据不同的边标签应用相应的文法规则
        switch (label)
        {
            case Addr:
                // PT → Addr
                addNewEdge(src, dst, PT);
                break;

            case Copy:
                // PT → Copy PT
                // 对于所有 src --Copy--> mid --PT--> dst
                if (succMap.count(dst) && succMap[dst].count(PT))
                {
                    for (auto target : succMap[dst][PT])
                    {
                        addNewEdge(src, target, PT);
                    }
                }
                // 对于所有 src --PT--> mid --CopyBar--> dst
                if (succMap.count(src) && succMap[src].count(PT))
                {
                    for (auto obj : succMap[src][PT])
                    {
                        addNewEdge(dst, obj, PT);
                    }
                }
                break;

            case PT:
                // PT → Copy PT
                // 对于所有 mid --Copy--> src --PT--> dst
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(Copy))
                {
                    for (auto pred : graph->getPredecessorMap()[src][Copy])
                    {
                        addNewEdge(pred, dst, PT);
                    }
                }
                // 对于所有 src --PT--> dst --CopyBar--> mid
                if (succMap.count(dst) && succMap[dst].count(CopyBar))
                {
                    for (auto succ : succMap[dst][CopyBar])
                    {
                        addNewEdge(src, succ, PT);
                    }
                }

                // SV → PT StoreBar
                if (succMap.count(dst) && succMap[dst].count(StoreBar))
                {
                    for (auto target : succMap[dst][StoreBar])
                    {
                        addNewEdge(src, target, SV);
                    }
                }

                // VP → VFBar PT
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(VFBar))
                {
                    for (auto pred : graph->getPredecessorMap()[src][VFBar])
                    {
                        addNewEdge(pred, dst, VP);
                    }
                }
                break;

            case Store:
                // SV → PT StoreBar
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(PT))
                {
                    for (auto pred : graph->getPredecessorMap()[src][PT])
                    {
                        addNewEdge(pred, dst, SV);
                    }
                }
                break;

            case StoreBar:
                // SV → PT StoreBar
                if (succMap.count(src) && succMap[src].count(PT))
                {
                    for (auto obj : succMap[src][PT])
                    {
                        addNewEdge(obj, dst, SV);
                    }
                }
                break;

            case Load:
                // VF → PT Load
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(PT))
                {
                    for (auto pred : graph->getPredecessorMap()[src][PT])
                    {
                        addNewEdge(pred, dst, VF);
                    }
                }
                break;

            case LoadBar:
                // VF → PT Load
                if (succMap.count(src) && succMap[src].count(PT))
                {
                    for (auto obj : succMap[src][PT])
                    {
                        addNewEdge(obj, dst, VF);
                    }
                }
                break;

            case SV:
                // PT → Store VF
                // 对于所有 src --SV--> mid --LoadBar--> dst
                if (succMap.count(dst) && succMap[dst].count(LoadBar))
                {
                    for (auto target : succMap[dst][LoadBar])
                    {
                        addNewEdge(src, target, PT);
                    }
                }
                // VA → SV SVBar
                if (succMap.count(dst) && succMap[dst].count(SVBar))
                {
                    for (auto target : succMap[dst][SVBar])
                    {
                        addNewEdge(src, target, VA);
                    }
                }
                break;

            case SVBar:
                // VA → SV SVBar
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(SV))
                {
                    for (auto pred : graph->getPredecessorMap()[src][SV])
                    {
                        addNewEdge(pred, dst, VA);
                    }
                }
                break;

            case VF:
                // PT → Store VF (等价于 SV LoadBar)
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(Store))
                {
                    for (auto pred : graph->getPredecessorMap()[src][Store])
                    {
                        addNewEdge(pred, dst, PT);
                    }
                }
                // PV → PT VFBar
                if (succMap.count(dst) && succMap[dst].count(VFBar))
                {
                    for (auto target : succMap[dst][VFBar])
                    {
                        addNewEdge(src, target, PV);
                    }
                }
                break;

            case VFBar:
                // VP → VFBar PT
                if (succMap.count(dst) && succMap[dst].count(PT))
                {
                    for (auto target : succMap[dst][PT])
                    {
                        addNewEdge(src, target, VP);
                    }
                }
                // PV → PT VFBar
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(PT))
                {
                    for (auto pred : graph->getPredecessorMap()[src][PT])
                    {
                        addNewEdge(pred, dst, PV);
                    }
                }
                break;

            case VA:
                // LV → VA VPBar
                if (succMap.count(dst) && succMap[dst].count(VPBar))
                {
                    for (auto target : succMap[dst][VPBar])
                    {
                        addNewEdge(src, target, LV);
                    }
                }
                break;

            case VP:
                // LV → VABar VP
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(VABar))
                {
                    for (auto pred : graph->getPredecessorMap()[src][VABar])
                    {
                        addNewEdge(pred, dst, LV);
                    }
                }
                break;

            case VPBar:
                // LV → VA VPBar
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(VA))
                {
                    for (auto pred : graph->getPredecessorMap()[src][VA])
                    {
                        addNewEdge(pred, dst, LV);
                    }
                }
                break;

            case VABar:
                // LV → VABar VP
                if (succMap.count(dst) && succMap[dst].count(VP))
                {
                    for (auto target : succMap[dst][VP])
                    {
                        addNewEdge(src, target, LV);
                    }
                }
                break;

            case PV:
                // PT → PV LVBar
                if (succMap.count(dst) && succMap[dst].count(LVBar))
                {
                    for (auto target : succMap[dst][LVBar])
                    {
                        addNewEdge(src, target, PT);
                    }
                }
                break;

            case LV:
                // PT → PVBar LV
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(PVBar))
                {
                    for (auto pred : graph->getPredecessorMap()[src][PVBar])
                    {
                        addNewEdge(pred, dst, PT);
                    }
                }
                break;

            case LVBar:
                // PT → PV LVBar
                if (graph->getPredecessorMap().count(src) && 
                    graph->getPredecessorMap()[src].count(PV))
                {
                    for (auto pred : graph->getPredecessorMap()[src][PV])
                    {
                        addNewEdge(pred, dst, PT);
                    }
                }
                break;

            case PVBar:
                // PT → PVBar LV
                if (succMap.count(dst) && succMap[dst].count(LV))
                {
                    for (auto target : succMap[dst][LV])
                    {
                        addNewEdge(src, target, PT);
                    }
                }
                break;

            default:
                break;
        }
    }
}

// 添加新边的辅助方法
void CFLR::addNewEdge(unsigned src, unsigned dst, EdgeLabel label)
{
    if (!graph->hasEdge(src, dst, label))
    {
        graph->addEdge(src, dst, label);
        workList.push(CFLREdge(src, dst, label));
    }
}
