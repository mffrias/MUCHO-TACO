package roops.core.objects;

//@ model import org.jmlspecs.lang.*;


public class BinomialHeapNode extends java.lang.Object {

  public int roops_core_objects_BinomialHeapNode_key;
  public int roops_core_objects_BinomialHeapNode_degree;
  public /*@ nullable @*/ roops.core.objects.BinomialHeapNode roops_core_objects_BinomialHeapNode_parent;
  public /*@ nullable @*/ roops.core.objects.BinomialHeapNode roops_core_objects_BinomialHeapNode_sibling;
  public /*@ nullable @*/ roops.core.objects.BinomialHeapNode roops_core_objects_BinomialHeapNode_child;

  public BinomialHeapNode() {
    this.roops_core_objects_BinomialHeapNode_key = (byte)0;
    this.roops_core_objects_BinomialHeapNode_degree = (byte)0;
    this.roops_core_objects_BinomialHeapNode_parent = ((roops.core.objects.BinomialHeapNode)(null));
    this.roops_core_objects_BinomialHeapNode_sibling = ((roops.core.objects.BinomialHeapNode)(null));
    this.roops_core_objects_BinomialHeapNode_child = ((roops.core.objects.BinomialHeapNode)(null));
    {
    }
  }


  public BinomialHeapNode(int value) {
    this.roops_core_objects_BinomialHeapNode_key = (byte)0;
    this.roops_core_objects_BinomialHeapNode_degree = (byte)0;
    this.roops_core_objects_BinomialHeapNode_parent = ((roops.core.objects.BinomialHeapNode)(null));
    this.roops_core_objects_BinomialHeapNode_sibling = ((roops.core.objects.BinomialHeapNode)(null));
    this.roops_core_objects_BinomialHeapNode_child = ((roops.core.objects.BinomialHeapNode)(null));
    {
      this.roops_core_objects_BinomialHeapNode_key = value;
      this.roops_core_objects_BinomialHeapNode_degree = 0;
      this.roops_core_objects_BinomialHeapNode_parent = ((roops.core.objects.BinomialHeapNode)(null));
      this.roops_core_objects_BinomialHeapNode_sibling = ((roops.core.objects.BinomialHeapNode)(null));
      this.roops_core_objects_BinomialHeapNode_child = ((roops.core.objects.BinomialHeapNode)(null));
    }
  }


  /*@ 
    @ requires true;
    @ ensures true;
    @*/
  public roops.core.objects.BinomialHeapNode reverse(roops.core.objects.BinomialHeapNode sibl) {
    {
      roops.core.objects.BinomialHeapNode param_sibl_26;

      param_sibl_26 = sibl;
      {
        boolean t_784;
        roops.core.objects.BinomialHeapNode var_145_ret;

        t_784 = this.roops_core_objects_BinomialHeapNode_sibling  !=  null;

        if (t_784) {
          {
            {
              {
                {
                  {
                    roops.core.objects.BinomialHeapNode t_783;

                    t_783 = this.roops_core_objects_BinomialHeapNode_sibling.reverse(this);
                    var_145_ret = t_783;
                  }
                }
              }
            }
          }
        } else {
          {
            {
              {
                {
                  {
                    var_145_ret = this;
                  }
                }
              }
            }
          }
        }
        this.roops_core_objects_BinomialHeapNode_sibling = param_sibl_26;
        if (true) return var_145_ret;
      }
    }

    return null;
  }


  /*@ 
    @ requires true;
    @ ensures true;
    @*/
  public roops.core.objects.BinomialHeapNode findMinNode() {
    {
      {
        roops.core.objects.BinomialHeapNode var_146_x = this, var_147_y = this;
        int var_148_min = var_146_x.roops_core_objects_BinomialHeapNode_key;

        {
          {
            boolean t_792;
            boolean t_793;
            boolean t_794;

            t_792 = var_146_x  !=  null;

            if (t_792) {
              {
                {
                  {
                    {
                      {
                        boolean t_791;

                        {
                          boolean t_785;

                          t_785 = var_146_x.roops_core_objects_BinomialHeapNode_key  <  var_148_min;

                          if (t_785) {
                            {
                              {
                                {
                                  {
                                    {
                                      var_147_y = var_146_x;
                                      var_148_min = var_146_x.roops_core_objects_BinomialHeapNode_key;
                                    }
                                  }
                                }
                              }
                            }
                          }
                          var_146_x = var_146_x.roops_core_objects_BinomialHeapNode_sibling;
                        }
                        t_791 = var_146_x  !=  null;
                        if (t_791) {
                          {
                            {
                              {
                                {
                                  {
                                    boolean t_790;

                                    {
                                      boolean t_786;

                                      t_786 = var_146_x.roops_core_objects_BinomialHeapNode_key  <  var_148_min;

                                      if (t_786) {
                                        {
                                          {
                                            {
                                              {
                                                {
                                                  var_147_y = var_146_x;
                                                  var_148_min = var_146_x.roops_core_objects_BinomialHeapNode_key;
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                      var_146_x = var_146_x.roops_core_objects_BinomialHeapNode_sibling;
                                    }
                                    t_790 = var_146_x  !=  null;
                                    if (t_790) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_789;

                                                {
                                                  boolean t_787;

                                                  t_787 = var_146_x.roops_core_objects_BinomialHeapNode_key  <  var_148_min;

                                                  if (t_787) {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            {
                                                              var_147_y = var_146_x;
                                                              var_148_min = var_146_x.roops_core_objects_BinomialHeapNode_key;
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                  var_146_x = var_146_x.roops_core_objects_BinomialHeapNode_sibling;
                                                }
                                                t_789 = var_146_x  !=  null;
                                                if (t_789) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            boolean t_788;

                                                            t_788 = var_146_x.roops_core_objects_BinomialHeapNode_key  <  var_148_min;

                                                            if (t_788) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        var_147_y = var_146_x;
                                                                        var_148_min = var_146_x.roops_core_objects_BinomialHeapNode_key;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                            var_146_x = var_146_x.roops_core_objects_BinomialHeapNode_sibling;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            t_793 = var_146_x  !=  null;
            t_794 = ! t_793;
            assert t_794;
          }
        }
        if (true) return var_147_y;
      }
    }

    return null;
  }


  public roops.core.objects.BinomialHeapNode findANodeWithKey(int value) {
    {
      int param_value_27;

      param_value_27 = value;
      {
        roops.core.objects.BinomialHeapNode var_149_temp = this, var_150_node = ((roops.core.objects.BinomialHeapNode)(null));

        {
          boolean var_151_breakVariable_8 = false;
          boolean var_152_breakVariable_7 = false;

          {
            boolean t_834;
            boolean t_835;
            boolean t_836;
            boolean t_837;
            boolean t_838;
            boolean t_839;
            boolean t_840;
            boolean t_841;
            boolean t_842;
            boolean t_843;
            boolean t_844;

            {
              t_835 = ! var_152_breakVariable_7;
              if (t_835) {
                {
                  {
                    t_837 = ! var_151_breakVariable_8;

                    if (t_837) {
                      {
                        {
                          t_838 = var_149_temp  !=  null;
                          if (t_838) {
                            {
                              t_836 = true;
                            }
                          } else {
                            {
                              t_836 = false;
                            }
                          }
                        }
                      }
                    } else {
                      {
                        t_836 = false;
                      }
                    }
                    if (t_836) {
                      {
                        t_834 = true;
                      }
                    } else {
                      {
                        t_834 = false;
                      }
                    }
                  }
                }
              } else {
                {
                  t_834 = false;
                }
              }
            }

            if (t_834) {
              {
                {
                  {
                    {
                      {
                        boolean t_829;
                        boolean t_830;
                        boolean t_831;
                        boolean t_832;
                        boolean t_833;

                        {
                          boolean t_795;
                          boolean t_800;

                          t_795 = var_149_temp.roops_core_objects_BinomialHeapNode_key  ==  param_value_27;

                          if (t_795) {
                            {
                              {
                                {
                                  {
                                    {
                                      var_150_node = var_149_temp;
                                      var_152_breakVariable_7 = true;
                                    }
                                  }
                                }
                              }
                            }
                          }
                          t_800 = ! var_152_breakVariable_7;
                          if (t_800) {
                            {
                              {
                                {
                                  {
                                    {
                                      boolean t_799;

                                      t_799 = ! var_152_breakVariable_7;
                                      if (t_799) {
                                        {
                                          {
                                            {
                                              {
                                                {
                                                  boolean t_798;

                                                  t_798 = var_149_temp.roops_core_objects_BinomialHeapNode_child  ==  null;
                                                  if (t_798) {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            {
                                                              var_149_temp = var_149_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  } else {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            {
                                                              roops.core.objects.BinomialHeapNode t_796;
                                                              boolean t_797;

                                                              t_796 = var_149_temp.roops_core_objects_BinomialHeapNode_child.findANodeWithKey(param_value_27);
                                                              var_150_node = t_796;
                                                              t_797 = var_150_node  ==  null;
                                                              if (t_797) {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        {
                                                                          var_149_temp = var_149_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              } else {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        {
                                                                          var_151_breakVariable_8 = true;
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                        {
                          t_830 = ! var_152_breakVariable_7;
                          if (t_830) {
                            {
                              {
                                t_832 = ! var_151_breakVariable_8;

                                if (t_832) {
                                  {
                                    {
                                      t_833 = var_149_temp  !=  null;
                                      if (t_833) {
                                        {
                                          t_831 = true;
                                        }
                                      } else {
                                        {
                                          t_831 = false;
                                        }
                                      }
                                    }
                                  }
                                } else {
                                  {
                                    t_831 = false;
                                  }
                                }
                                if (t_831) {
                                  {
                                    t_829 = true;
                                  }
                                } else {
                                  {
                                    t_829 = false;
                                  }
                                }
                              }
                            }
                          } else {
                            {
                              t_829 = false;
                            }
                          }
                        }
                        if (t_829) {
                          {
                            {
                              {
                                {
                                  {
                                    boolean t_824;
                                    boolean t_825;
                                    boolean t_826;
                                    boolean t_827;
                                    boolean t_828;

                                    {
                                      boolean t_801;
                                      boolean t_806;

                                      t_801 = var_149_temp.roops_core_objects_BinomialHeapNode_key  ==  param_value_27;

                                      if (t_801) {
                                        {
                                          {
                                            {
                                              {
                                                {
                                                  var_150_node = var_149_temp;
                                                  var_152_breakVariable_7 = true;
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                      t_806 = ! var_152_breakVariable_7;
                                      if (t_806) {
                                        {
                                          {
                                            {
                                              {
                                                {
                                                  boolean t_805;

                                                  t_805 = ! var_152_breakVariable_7;
                                                  if (t_805) {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            {
                                                              boolean t_804;

                                                              t_804 = var_149_temp.roops_core_objects_BinomialHeapNode_child  ==  null;
                                                              if (t_804) {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        {
                                                                          var_149_temp = var_149_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              } else {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        {
                                                                          roops.core.objects.BinomialHeapNode t_802;
                                                                          boolean t_803;

                                                                          t_802 = var_149_temp.roops_core_objects_BinomialHeapNode_child.findANodeWithKey(param_value_27);
                                                                          var_150_node = t_802;
                                                                          t_803 = var_150_node  ==  null;
                                                                          if (t_803) {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    {
                                                                                      var_149_temp = var_149_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          } else {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    {
                                                                                      var_151_breakVariable_8 = true;
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                    {
                                      t_825 = ! var_152_breakVariable_7;
                                      if (t_825) {
                                        {
                                          {
                                            t_827 = ! var_151_breakVariable_8;

                                            if (t_827) {
                                              {
                                                {
                                                  t_828 = var_149_temp  !=  null;
                                                  if (t_828) {
                                                    {
                                                      t_826 = true;
                                                    }
                                                  } else {
                                                    {
                                                      t_826 = false;
                                                    }
                                                  }
                                                }
                                              }
                                            } else {
                                              {
                                                t_826 = false;
                                              }
                                            }
                                            if (t_826) {
                                              {
                                                t_824 = true;
                                              }
                                            } else {
                                              {
                                                t_824 = false;
                                              }
                                            }
                                          }
                                        }
                                      } else {
                                        {
                                          t_824 = false;
                                        }
                                      }
                                    }
                                    if (t_824) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_819;
                                                boolean t_820;
                                                boolean t_821;
                                                boolean t_822;
                                                boolean t_823;

                                                {
                                                  boolean t_807;
                                                  boolean t_812;

                                                  t_807 = var_149_temp.roops_core_objects_BinomialHeapNode_key  ==  param_value_27;

                                                  if (t_807) {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            {
                                                              var_150_node = var_149_temp;
                                                              var_152_breakVariable_7 = true;
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                  t_812 = ! var_152_breakVariable_7;
                                                  if (t_812) {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            {
                                                              boolean t_811;

                                                              t_811 = ! var_152_breakVariable_7;
                                                              if (t_811) {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        {
                                                                          boolean t_810;

                                                                          t_810 = var_149_temp.roops_core_objects_BinomialHeapNode_child  ==  null;
                                                                          if (t_810) {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    {
                                                                                      var_149_temp = var_149_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          } else {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    {
                                                                                      roops.core.objects.BinomialHeapNode t_808;
                                                                                      boolean t_809;

                                                                                      t_808 = var_149_temp.roops_core_objects_BinomialHeapNode_child.findANodeWithKey(param_value_27);
                                                                                      var_150_node = t_808;
                                                                                      t_809 = var_150_node  ==  null;
                                                                                      if (t_809) {
                                                                                        {
                                                                                          {
                                                                                            {
                                                                                              {
                                                                                                {
                                                                                                  var_149_temp = var_149_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                                                                }
                                                                                              }
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      } else {
                                                                                        {
                                                                                          {
                                                                                            {
                                                                                              {
                                                                                                {
                                                                                                  var_151_breakVariable_8 = true;
                                                                                                }
                                                                                              }
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                                {
                                                  t_820 = ! var_152_breakVariable_7;
                                                  if (t_820) {
                                                    {
                                                      {
                                                        t_822 = ! var_151_breakVariable_8;

                                                        if (t_822) {
                                                          {
                                                            {
                                                              t_823 = var_149_temp  !=  null;
                                                              if (t_823) {
                                                                {
                                                                  t_821 = true;
                                                                }
                                                              } else {
                                                                {
                                                                  t_821 = false;
                                                                }
                                                              }
                                                            }
                                                          }
                                                        } else {
                                                          {
                                                            t_821 = false;
                                                          }
                                                        }
                                                        if (t_821) {
                                                          {
                                                            t_819 = true;
                                                          }
                                                        } else {
                                                          {
                                                            t_819 = false;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  } else {
                                                    {
                                                      t_819 = false;
                                                    }
                                                  }
                                                }
                                                if (t_819) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            boolean t_813;
                                                            boolean t_818;

                                                            t_813 = var_149_temp.roops_core_objects_BinomialHeapNode_key  ==  param_value_27;

                                                            if (t_813) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        var_150_node = var_149_temp;
                                                                        var_152_breakVariable_7 = true;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                            t_818 = ! var_152_breakVariable_7;
                                                            if (t_818) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        boolean t_817;

                                                                        t_817 = ! var_152_breakVariable_7;
                                                                        if (t_817) {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    boolean t_816;

                                                                                    t_816 = var_149_temp.roops_core_objects_BinomialHeapNode_child  ==  null;
                                                                                    if (t_816) {
                                                                                      {
                                                                                        {
                                                                                          {
                                                                                            {
                                                                                              {
                                                                                                var_149_temp = var_149_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                                                              }
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    } else {
                                                                                      {
                                                                                        {
                                                                                          {
                                                                                            {
                                                                                              {
                                                                                                roops.core.objects.BinomialHeapNode t_814;
                                                                                                boolean t_815;

                                                                                                t_814 = var_149_temp.roops_core_objects_BinomialHeapNode_child.findANodeWithKey(param_value_27);
                                                                                                var_150_node = t_814;
                                                                                                t_815 = var_150_node  ==  null;
                                                                                                if (t_815) {
                                                                                                  {
                                                                                                    {
                                                                                                      {
                                                                                                        {
                                                                                                          {
                                                                                                            var_149_temp = var_149_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                                                                          }
                                                                                                        }
                                                                                                      }
                                                                                                    }
                                                                                                  }
                                                                                                } else {
                                                                                                  {
                                                                                                    {
                                                                                                      {
                                                                                                        {
                                                                                                          {
                                                                                                            var_151_breakVariable_8 = true;
                                                                                                          }
                                                                                                        }
                                                                                                      }
                                                                                                    }
                                                                                                  }
                                                                                                }
                                                                                              }
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            {
              t_840 = ! var_152_breakVariable_7;
              if (t_840) {
                {
                  {
                    t_842 = ! var_151_breakVariable_8;

                    if (t_842) {
                      {
                        {
                          t_843 = var_149_temp  !=  null;
                          if (t_843) {
                            {
                              t_841 = true;
                            }
                          } else {
                            {
                              t_841 = false;
                            }
                          }
                        }
                      }
                    } else {
                      {
                        t_841 = false;
                      }
                    }
                    if (t_841) {
                      {
                        t_839 = true;
                      }
                    } else {
                      {
                        t_839 = false;
                      }
                    }
                  }
                }
              } else {
                {
                  t_839 = false;
                }
              }
            }
            t_844 = ! t_839;
            assert t_844;
          }
        }
        if (true) return var_150_node;
      }
    }

    return null;
  }


  public int getSize() {
    {
      {
        boolean t_852;

        t_852 = this.roops_core_objects_BinomialHeapNode_child  ==  null;
        if (t_852) {
          {
            {
              {
                {
                  {
                    if (true) return 1;
                  }
                }
              }
            }
          }
        } else {
          {
            {
              {
                {
                  {
                    boolean t_851;

                    t_851 = this.roops_core_objects_BinomialHeapNode_sibling  ==  null;
                    if (t_851) {
                      {
                        {
                          {
                            {
                              {
                                int t_845;
                                int t_846;

                                t_845 = this.roops_core_objects_BinomialHeapNode_child.getSize();
                                t_846 = 1 + t_845;
                                if (true) return t_846;
                              }
                            }
                          }
                        }
                      }
                    } else {
                      {
                        {
                          {
                            {
                              {
                                int t_847;
                                int t_848;
                                int t_849;
                                int t_850;

                                t_847 = this.roops_core_objects_BinomialHeapNode_child.getSize();
                                t_848 = 1 + t_847;
                                t_849 = this.roops_core_objects_BinomialHeapNode_sibling.getSize();
                                t_850 = t_848 + t_849;
                                if (true) return t_850;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    return (byte)0;
  }

}
