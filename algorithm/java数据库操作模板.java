			try {
				Class.forName("com.mysql.jdbc.Driver");
				conn = DriverManager.getConnection("jdbc:mysql://127.0.0.1:3306/ShoppingApp","root","dfsbfs");
				pstmt = conn.prepareStatement("");
				//
				
				
				rs = pstmt.executeQuery();
				
				
			} catch (ClassNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (SQLException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}finally
			{
				try{
					if(rs!=null)
					{
						rs.close();rs=null;
					}
					if(stmt!=null)
					{
						stmt.close();stmt=null;
					}
					if(conn!=null)
					{
						conn.close();conn=null;
					}
					
				} catch (SQLException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}finally{}
			}




